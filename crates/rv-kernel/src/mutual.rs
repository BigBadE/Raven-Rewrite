//! **Mutual** (simultaneously-declared) inductive families — the non-indexed case.
//!
//! A mutual group `I₀ … I_{g-1}` shares a parameter telescope and may reference one
//! another in their constructors (`Tree`/`Forest`, `Even`/`Odd`, …). The whole group is
//! installed together, and **each** type gets a recursor that takes a motive for *every*
//! type in the group and a minor premise for *every* constructor of *every* type; a
//! recursive field of type `I_s` contributes an induction hypothesis built from `I_s`'s
//! motive, and the ι-rules cross-call the sibling recursors. This reuses the same de
//! Bruijn machinery as the single-inductive generator ([`crate::generate`]) — the only
//! new structure is the *band of g motives* sitting before the minor premises (tracked by
//! [`crate::env::Recursor::num_motives`]).
//!
//! Scope: non-indexed members (`I_t : Π params. Sort`), strictly-positive recursive
//! fields (direct `I_s params`, no W-types). Indexed mutual families (`Even : Nat →
//! Prop`) are a future extension.

use crate::check::Checker;
use crate::env::{Constructor, Decl, Env, Inductive, RecRule, Recursor};
use crate::generate::{ctx_images, fold_pis, mk_var, occurs, peel_all_pis, peel_pis, IndSpec};
use crate::level::Level;
use crate::term::{Name, Term};
use std::collections::HashMap;
use std::rc::Rc;

/// A constructor field's relationship to the mutual group.
enum FieldKind {
    /// No group member occurs: an ordinary argument.
    NonRec,
    /// A direct recursive argument into group member `into`.
    Rec { into: usize },
}

/// Per-constructor data threaded from checking into recursor synthesis.
struct CInfo {
    name: Name,
    /// Which group member this constructor builds.
    ind_index: usize,
    /// This constructor's position among *its own* type's constructors (its tag).
    local_index: usize,
    fields: Vec<Term>,
    kinds: Vec<FieldKind>,
}

/// Declare a mutual group of non-indexed inductives. A single-element group is just an
/// ordinary inductive (delegated to [`crate::generate::declare_inductive`]).
pub fn declare_mutual(env: &mut Env, specs: Vec<IndSpec>) -> Result<(), String> {
    let g = specs.len();
    if g == 0 {
        return Err("empty mutual block".into());
    }
    if g == 1 {
        return crate::generate::declare_inductive(env, specs.into_iter().next().unwrap());
    }
    let num_levels = specs[0].num_levels;
    let k = specs[0].num_params;
    for s in &specs {
        if s.num_levels != num_levels || s.num_params != k {
            return Err("mutual inductives must share universe parameters and parameters".into());
        }
    }
    let ind_levels: Vec<Level> = (0..num_levels).map(Level::param).collect();

    // 1. Type-check every former; require each to be non-indexed (`Π params. Sort`).
    let mut param_doms: Vec<Term> = Vec::new();
    let mut result_levels: Vec<Level> = Vec::new();
    for (i, s) in specs.iter().enumerate() {
        Checker::new(env)
            .infer_closed(&s.ty)
            .map_err(|e| format!("type former '{}': {e}", s.name))?;
        let (pdoms, after) = peel_pis(s.ty.clone(), k)
            .ok_or_else(|| format!("'{}' has fewer than {k} parameters", s.name))?;
        let result_level = match &after {
            Term::Sort(l) => l.clone(),
            _ => {
                return Err(format!(
                    "mutual member '{}' must be non-indexed (`Π params. Sort`); indexed \
                     mutual inductives are not yet supported",
                    s.name
                ))
            }
        };
        if i == 0 {
            param_doms = pdoms;
        }
        result_levels.push(result_level);
    }

    // 2. Install all type formers first, so constructors may cross-reference them.
    let group_names: Vec<Name> = specs.iter().map(|s| s.name.clone()).collect();
    for s in &specs {
        let ctor_names: Vec<Name> = s.ctors.iter().map(|c| c.name.clone()).collect();
        env.insert(
            s.name.clone(),
            Decl::Inductive(Rc::new(Inductive {
                num_levels,
                ty: s.ty.clone(),
                num_params: k,
                num_indices: 0,
                ctors: ctor_names,
                recursor: s.rec_name.clone(),
                group: group_names.clone(),
            })),
        )?;
    }
    let group: Vec<String> = specs.iter().map(|s| s.name.to_string()).collect();

    // 3. Check every constructor (well-typed, strictly positive, concludes in its type),
    //    classifying fields against the whole group.
    let mut infos: Vec<CInfo> = Vec::new();
    for (ti, s) in specs.iter().enumerate() {
        for (li, c) in s.ctors.iter().enumerate() {
            Checker::new(env)
                .infer_closed(&c.ty)
                .map_err(|e| format!("constructor '{}': {e}", c.name))?;
            let (_p, rest) = peel_pis(c.ty.clone(), k)
                .ok_or_else(|| format!("constructor '{}' has fewer than {k} parameters", c.name))?;
            let (fields, concl) = peel_all_pis(rest);
            let (head, cargs) = concl.unfold_apps();
            match &head {
                Term::Const(h, _) if **h == *s.name => {}
                _ => {
                    return Err(format!(
                        "constructor '{}' must conclude in '{}'",
                        c.name, s.name
                    ))
                }
            }
            if cargs.len() != k {
                return Err(format!("constructor '{}' conclusion is mis-applied", c.name));
            }
            let kinds = fields
                .iter()
                .map(|f| classify(&group, k, f))
                .collect::<Result<Vec<_>, _>>()?;
            infos.push(CInfo { name: c.name.clone(), ind_index: ti, local_index: li, fields, kinds });
        }
    }

    // 4. Install constructors.
    for info in &infos {
        let s = &specs[info.ind_index];
        env.insert(
            info.name.clone(),
            Decl::Constructor(Rc::new(Constructor {
                num_levels,
                ty: s.ctors[info.local_index].ty.clone(),
                ind: s.name.clone(),
                index: info.local_index,
                num_fields: info.fields.len(),
            })),
        )?;
    }

    // 5. Large-elimination: allow only if no member is a (non-trivial) `Prop`; otherwise
    //    pin elimination to `Prop` (conservative but sound).
    let all_non_prop = result_levels.iter().all(|l| !matches!(l.normalize(), Level::Zero));
    let (rec_num_levels, elim_u) = if all_non_prop {
        (num_levels + 1, Level::param(num_levels))
    } else {
        (num_levels, Level::Zero)
    };
    let big_m = infos.len();

    // Layout shared by *every* recursor in the group:
    //   [ params(k) | motives(g) | minors(M) | major(1) ]
    let ind_app = |tt: usize, depth: usize| -> Term {
        let mut t = Term::cnst(specs[tt].name.clone(), ind_levels.clone());
        for j in 0..k {
            t = Term::app(t, mk_var(depth, j));
        }
        t
    };
    // Motive domains: C_t : I_t params → Sort elim_u, the t-th binder (at depth k+t).
    let motive_doms: Vec<Term> = (0..g)
        .map(|tt| Term::pi(ind_app(tt, k + tt), Term::Sort(elim_u.clone())))
        .collect();
    // Minor domains (one per constructor of any type).
    let minor_doms: Vec<Term> = infos
        .iter()
        .enumerate()
        .map(|(gi, info)| build_minor(&ind_levels, k, g, k + g + gi, info))
        .collect();

    // 6. One recursor per type. Same params/motives/minors prefix; the major and the
    //    conclusion are that type's.
    for (j, s) in specs.iter().enumerate() {
        let d_major = k + g + big_m;
        let major_dom = ind_app(j, d_major);
        let d_concl = d_major + 1;
        let cj = mk_var(d_concl, k + j); // motive C_j
        let concl = Term::app(cj, mk_var(d_concl, k + g + big_m)); // C_j major

        let mut all_doms = param_doms.clone();
        all_doms.extend(motive_doms.iter().cloned());
        all_doms.extend(minor_doms.iter().cloned());
        all_doms.push(major_dom);
        let rec_ty = fold_pis(&all_doms, concl);

        // ι-rules fire only on *this* type's constructors (its recursor's major is I_j).
        let mut rules: HashMap<Name, RecRule> = HashMap::new();
        for (gi, info) in infos.iter().enumerate() {
            if info.ind_index != j {
                continue;
            }
            let rhs = build_rule_rhs(&specs, rec_num_levels, k, g, big_m, gi, info);
            rules.insert(
                info.name.clone(),
                RecRule { ctor: info.name.clone(), num_fields: info.fields.len(), rhs },
            );
        }

        env.insert(
            s.rec_name.clone(),
            Decl::Recursor(Rc::new(Recursor {
                num_levels: rec_num_levels,
                ty: rec_ty,
                ind: s.name.clone(),
                num_params: k,
                num_motives: g,
                num_indices: 0,
                num_minors: big_m,
                rules,
            })),
        )?;
    }
    Ok(())
}

/// Classify a constructor field against the mutual group (strict positivity enforced).
fn classify(group: &[String], k: usize, a: &Term) -> Result<FieldKind, String> {
    if !group.iter().any(|n| occurs(n, a)) {
        return Ok(FieldKind::NonRec);
    }
    let (doms, body) = peel_all_pis(a.clone());
    for d in &doms {
        if group.iter().any(|n| occurs(n, d)) {
            return Err("non-strictly-positive occurrence in a mutual field".into());
        }
    }
    if !doms.is_empty() {
        return Err("recursive mutual argument under a binder (W-type) is not supported".into());
    }
    let (head, args) = body.unfold_apps();
    match &head {
        Term::Const(h, _) => match group.iter().position(|n| *n == **h) {
            Some(into) if args.len() == k => Ok(FieldKind::Rec { into }),
            Some(_) => Err("recursive mutual occurrence is mis-applied".into()),
            None => Err("a group member occurs in a non-positive position".into()),
        },
        _ => Err("a group member occurs in a non-positive position".into()),
    }
}

/// Build the minor premise for one constructor at base depth `d0`. The motive band sits
/// at levels `k..k+g`; a recursive field into `I_s` gets `ih : C_s field`.
fn build_minor(ind_levels: &[Level], k: usize, _g: usize, d0: usize, info: &CInfo) -> Term {
    let mut doms: Vec<Term> = Vec::new();
    let mut field_levels: Vec<usize> = Vec::new();
    let mut d = d0;
    for (field_ty, kind) in info.fields.iter().zip(&info.kinds) {
        // Re-express the field type in the minor context. Field types never mention the
        // motives, and params keep levels `0..k`, so the single-inductive `ctx_images`
        // (over `[params, prior fields]`) applies unchanged.
        let images = ctx_images(d, &field_levels, k);
        doms.push(field_ty.subst_ctx(&images));
        let this_field_level = d;
        field_levels.push(this_field_level);
        d += 1;
        if let FieldKind::Rec { into } = kind {
            // ih : C_into a_l
            let ih = Term::app(mk_var(d, k + into), mk_var(d, this_field_level));
            doms.push(ih);
            d += 1;
        }
    }
    // conclusion: C_t (ctor params fields)
    let d_mc = d;
    let mut ctor_app = Term::cnst(info.name.clone(), ind_levels.to_vec());
    for j in 0..k {
        ctor_app = Term::app(ctor_app, mk_var(d_mc, j));
    }
    for &fl in &field_levels {
        ctor_app = Term::app(ctor_app, mk_var(d_mc, fl));
    }
    let body = Term::app(mk_var(d_mc, k + info.ind_index), ctor_app);
    fold_pis(&doms, body)
}

/// Build the ι-rule right-hand side for one constructor: applied to
/// `[params…, motives…, minors…, fields…]`, it invokes the minor on the fields, with each
/// recursive field's hypothesis computed by the **sibling** recursor `I_into.rec`.
fn build_rule_rhs(
    specs: &[IndSpec],
    rec_num_levels: u32,
    k: usize,
    g: usize,
    big_m: usize,
    gi: usize,
    info: &CInfo,
) -> Term {
    let n = info.fields.len();
    let d = k + g + big_m + n; // [params, motives, minors, fields] all bound
    let rec_levels: Vec<Level> = (0..rec_num_levels).map(Level::param).collect();
    let field_level = |l: usize| k + g + big_m + l;

    let mut args: Vec<Term> = Vec::new();
    for (l, kind) in info.kinds.iter().enumerate() {
        args.push(mk_var(d, field_level(l)));
        if let FieldKind::Rec { into } = kind {
            // ih = I_into.rec params motives… minors… a_l
            let mut call = Term::cnst(specs[*into].rec_name.clone(), rec_levels.clone());
            for j in 0..k {
                call = Term::app(call, mk_var(d, j));
            }
            for t in 0..g {
                call = Term::app(call, mk_var(d, k + t)); // motives
            }
            for mm in 0..big_m {
                call = Term::app(call, mk_var(d, k + g + mm)); // minors
            }
            call = Term::app(call, mk_var(d, field_level(l))); // major = the field
            args.push(call);
        }
    }
    // The minor for this constructor is at level k+g+gi.
    let mut body = mk_var(d, k + g + gi);
    for a in args {
        body = Term::app(body, a);
    }
    let mut t = body;
    for _ in 0..d {
        t = Term::lam(Term::prop(), t);
    }
    t
}
