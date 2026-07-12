//! **Mutual** (simultaneously-declared) inductive families — including the
//! **indexed** case.
//!
//! A mutual group `I₀ … I_{g-1}` shares a parameter telescope and may reference one
//! another in their constructors (`Tree`/`Forest`, `Even`/`Odd`, …). Each member may
//! *also* carry its own index telescope (`Ev : Nat → Prop`, `Od : Nat → Prop`), i.e.
//! be a genuine indexed inductive **family**. The whole group is installed together,
//! and **each** type gets a recursor that takes a motive for *every* type in the group
//! and a minor premise for *every* constructor of *every* type; a recursive field of
//! type `I_s idx…` contributes an induction hypothesis built from `I_s`'s motive
//! (applied to that occurrence's index arguments), and the ι-rules cross-call the
//! sibling recursors.
//!
//! ## Layout
//!
//! Every recursor in the group shares the prefix
//!
//! ```text
//!   [ params(k) | motives(g) | minors(M) ]
//! ```
//!
//! and then, for the recursor of member `j`, continues with *that member's own*
//! indices and its major premise:
//!
//! ```text
//!   … | indices_j(m_j) | major : I_j params indices_j ]   ⟶   C_j indices_j major
//! ```
//!
//! The motive of member `t` abstracts over `t`'s indices:
//! `C_t : Π indices_t. (I_t params indices_t) → Sort u`. Because the index counts
//! `m_t` vary per member, each recursor stores its own [`Recursor::num_indices`]; the
//! shared prefix `params + motives + minors` does not.
//!
//! ## Scope / restrictions
//!
//! * Uniform parameters shared by the whole group; each member's *indices* are its own.
//! * Strictly-positive recursive fields that are **direct** (`I_s params indices`, no
//!   `W`-type / function-typed recursion). A recursive occurrence must supply the group
//!   parameters verbatim (uniform parameters); its *index* arguments are arbitrary.
//! * Non-nested (a group member may not occur as a parameter/index of another inductive
//!   inside a field).
//!
//! This reuses the same de Bruijn machinery as the single-inductive generator
//! ([`crate::generate`]); the new structure over the non-indexed mutual case is (a) the
//! per-member index telescopes threaded through motives, minors, and ι-rules, and (b)
//! the index/large-elimination handling matching [`crate::generate::declare_inductive`].

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
    /// A direct recursive argument into group member `into`, carrying that
    /// occurrence's index arguments (each expressed in the constructor's telescope
    /// context `[params, prior fields]`).
    Rec { into: usize, index_args: Vec<Term> },
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
    /// The index arguments this constructor pins in its conclusion `I_t params idx…`
    /// (in the telescope context `[params, all fields]`).
    concl_index_args: Vec<Term>,
}

/// Declare a mutual group of (possibly indexed) inductives. A single-element group is
/// just an ordinary inductive (delegated to [`crate::generate::declare_inductive`]).
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

    // 1. Type-check every former; split into shared params / per-member indices / sort.
    let mut param_doms: Vec<Term> = Vec::new();
    let mut index_doms: Vec<Vec<Term>> = Vec::with_capacity(g); // per member, in its own ctx
    let mut num_indices: Vec<usize> = Vec::with_capacity(g);
    let mut result_levels: Vec<Level> = Vec::new();
    for (i, s) in specs.iter().enumerate() {
        Checker::new(env)
            .infer_closed(&s.ty)
            .map_err(|e| format!("type former '{}': {e}", s.name))?;
        let (pdoms, after) = peel_pis(s.ty.clone(), k)
            .ok_or_else(|| format!("'{}' has fewer than {k} parameters", s.name))?;
        let (idoms, result) = peel_all_pis(after);
        let result_level = match &result {
            Term::Sort(l) => l.clone(),
            other => {
                return Err(format!(
                    "type former '{}' must end in a sort, found {other:?}",
                    s.name
                ))
            }
        };
        if i == 0 {
            param_doms = pdoms;
        }
        num_indices.push(idoms.len());
        index_doms.push(idoms);
        result_levels.push(result_level);
    }

    // 2. Install all type formers first, so constructors may cross-reference them.
    let group_names: Vec<Name> = specs.iter().map(|s| s.name.clone()).collect();
    for (i, s) in specs.iter().enumerate() {
        let ctor_names: Vec<Name> = s.ctors.iter().map(|c| c.name.clone()).collect();
        env.insert(
            s.name.clone(),
            Decl::Inductive(Rc::new(Inductive {
                num_levels,
                ty: s.ty.clone(),
                num_params: k,
                num_indices: num_indices[i],
                ctors: ctor_names,
                recursor: s.rec_name.clone(),
                group: group_names.clone(),
            })),
        )?;
    }
    let group: Vec<String> = specs.iter().map(|s| s.name.to_string()).collect();

    // 3. Check every constructor (well-typed, strictly positive, concludes in its type),
    //    classifying fields against the whole group and recording conclusion indices.
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
            if cargs.len() < k {
                return Err(format!("constructor '{}' conclusion is under-applied", c.name));
            }
            let concl_index_args = cargs[k..].to_vec();
            let kinds = fields
                .iter()
                .map(|f| classify(&group, k, f))
                .collect::<Result<Vec<_>, _>>()?;
            infos.push(CInfo {
                name: c.name.clone(),
                ind_index: ti,
                local_index: li,
                fields,
                kinds,
                concl_index_args,
            });
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
    //    pin elimination to `Prop` (conservative but sound). A group is large-eliminable
    //    if every member is non-`Prop`, or the whole group is a single-constructor,
    //    all-proof-field subsingleton family. To stay conservative and simple we require
    //    *all* members non-`Prop` for large elimination (the subsingleton escape hatch of
    //    the single case is not extended to genuine mutual groups).
    let all_non_prop = result_levels.iter().all(|l| !matches!(l.normalize(), Level::Zero));
    let (rec_num_levels, elim_u) = if all_non_prop {
        (num_levels + 1, Level::param(num_levels))
    } else {
        (num_levels, Level::Zero)
    };
    let big_m = infos.len();

    // Fully-applied `I_t params indices` where the params live at levels `0..k` and the
    // `idx_terms` are given explicitly (already at depth `depth`).
    let ind_app = |tt: usize, depth: usize, idx_terms: &[Term]| -> Term {
        let mut t = Term::cnst(specs[tt].name.clone(), ind_levels.clone());
        for j in 0..k {
            t = Term::app(t, mk_var(depth, j));
        }
        for s in idx_terms {
            t = Term::app(t, s.clone());
        }
        t
    };

    // Motive domains: `C_t : Π indices_t. (I_t params indices_t) → Sort u`. Motive `t`'s
    // binder sits after the `k` params and the `t` preceding motive binders, so its body
    // lives at *absolute* base depth `k + t`; the shared params are free variables there,
    // at absolute levels `0..k`. The source index domain `index_doms[t][l]` lives in the
    // former's own context `[params, idx_0..idx_{l-1}]`; re-expressed here, params must
    // shift up past the `t` preceding motive binders while prior index binders keep their
    // relative offset — a lift of `t` with cutoff `l`.
    let motive_doms: Vec<Term> = (0..g)
        .map(|tt| {
            let m_t = num_indices[tt];
            let inner_doms: Vec<Term> = index_doms[tt]
                .iter()
                .enumerate()
                .map(|(l, jd)| jd.lift(tt as isize, l))
                .collect();
            let dmid = k + tt + m_t; // absolute depth at the scrutinee position
            let idx_terms: Vec<Term> = (0..m_t).map(|l| mk_var(dmid, k + tt + l)).collect();
            let mut all: Vec<Term> = inner_doms;
            all.push(ind_app(tt, dmid, &idx_terms));
            fold_pis(&all, Term::Sort(elim_u.clone()))
        })
        .collect();

    // Minor domains (one per constructor of any type). The motive band sits at levels
    // `k..k+g`; the minor for constructor `gi` starts at depth `k+g+gi`.
    let minor_doms: Vec<Term> = infos
        .iter()
        .enumerate()
        .map(|(gi, info)| build_minor(&specs, &ind_levels, k, g, k + g + gi, info))
        .collect();

    // 6. One recursor per type. Same params/motives/minors prefix; then that member's
    //    indices, its major, and the conclusion `C_j indices_j major`.
    for (j, s) in specs.iter().enumerate() {
        let m_j = num_indices[j];
        // top-level index domains for member j: J_l originally referred to params by
        // levels 0..k; here they sit after motives+minors, so params are unchanged
        // (still 0..k) but we must shift *nothing* about params — however the index
        // domains may reference earlier index binders which now sit at k+g+M.. . The
        // source index domain `index_doms[j][l]` is in context [params, idx_0..idx_{l-1}]
        // with params at the bottom; re-expressing it in [params, motives, minors,
        // idx_0..idx_{l-1}] means params keep levels 0..k and prior indices keep their
        // relative offset. `subst_ctx` with images = [params identity] handles the shift
        // of the params past the inserted motive+minor block.
        let shift = (g + big_m) as isize;
        let top_index_doms: Vec<Term> = index_doms[j]
            .iter()
            .enumerate()
            .map(|(l, jd)| jd.lift(shift, l))
            .collect();

        let d_major = k + g + big_m + m_j;
        let major_idx: Vec<Term> = (0..m_j).map(|l| mk_var(d_major, k + g + big_m + l)).collect();
        let major_dom = ind_app(j, d_major, &major_idx);

        let d_concl = d_major + 1;
        let mut concl = mk_var(d_concl, k + j); // motive C_j
        for l in 0..m_j {
            concl = Term::app(concl, mk_var(d_concl, k + g + big_m + l)); // indices
        }
        concl = Term::app(concl, mk_var(d_concl, k + g + big_m + m_j)); // major

        let mut all_doms = param_doms.clone();
        all_doms.extend(motive_doms.iter().cloned());
        all_doms.extend(minor_doms.iter().cloned());
        all_doms.extend(top_index_doms);
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
                num_indices: m_j,
                num_minors: big_m,
                rules,
            })),
        )?;
    }
    Ok(())
}

/// Classify a constructor field against the mutual group (strict positivity enforced).
/// A recursive field must be a *direct* application `I_into params indices` where the
/// first `k` arguments are the uniform parameters and the rest are (arbitrary) indices.
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
            Some(into) if args.len() >= k => {
                Ok(FieldKind::Rec { into, index_args: args[k..].to_vec() })
            }
            Some(_) => Err("recursive mutual occurrence is under-applied".into()),
            None => Err("a group member occurs in a non-positive position".into()),
        },
        _ => Err("a group member occurs in a non-positive position".into()),
    }
}

/// Build the minor premise for one constructor at base depth `d0`. The motive band sits
/// at levels `k..k+g`; a recursive field into `I_s idx…` gets `ih : C_s idx' a_l`, and
/// the conclusion is `C_t concl_idx' (ctor params fields)`.
fn build_minor(
    _specs: &[IndSpec],
    ind_levels: &[Level],
    k: usize,
    _g: usize,
    d0: usize,
    info: &CInfo,
) -> Term {
    let mut doms: Vec<Term> = Vec::new();
    let mut field_levels: Vec<usize> = Vec::new();
    let mut d = d0;
    for (l, (field_ty, kind)) in info.fields.iter().zip(&info.kinds).enumerate() {
        // Re-express the field type in the minor context. Field types never mention the
        // motives, and params keep levels `0..k`, so the single-inductive `ctx_images`
        // (over `[params, prior fields]`) applies unchanged.
        let images = ctx_images(d, &field_levels, k);
        doms.push(field_ty.subst_ctx(&images));
        let this_field_level = d;
        field_levels.push(this_field_level);
        d += 1;
        if let FieldKind::Rec { into, index_args } = kind {
            // ih : C_into idx' a_l   (idx args re-expressed in the ctx of prior fields)
            let imgs = ctx_images(d, &field_levels[..l], k);
            let idx_imgs: Vec<Term> = index_args.iter().map(|s| s.subst_ctx(&imgs)).collect();
            let mut ih = mk_var(d, k + into);
            for s in &idx_imgs {
                ih = Term::app(ih, s.clone());
            }
            ih = Term::app(ih, mk_var(d, this_field_level));
            doms.push(ih);
            d += 1;
        }
    }
    // conclusion: C_t concl_idx' (ctor params fields)
    let d_mc = d;
    let imgs = ctx_images(d_mc, &field_levels, k);
    let concl_idx: Vec<Term> =
        info.concl_index_args.iter().map(|s| s.subst_ctx(&imgs)).collect();
    let mut ctor_app = Term::cnst(info.name.clone(), ind_levels.to_vec());
    for j in 0..k {
        ctor_app = Term::app(ctor_app, mk_var(d_mc, j));
    }
    for &fl in &field_levels {
        ctor_app = Term::app(ctor_app, mk_var(d_mc, fl));
    }
    let mut body = mk_var(d_mc, k + info.ind_index); // motive C_t
    for s in &concl_idx {
        body = Term::app(body, s.clone());
    }
    body = Term::app(body, ctor_app);
    fold_pis(&doms, body)
}

/// Build the ι-rule right-hand side for one constructor: applied to
/// `[params…, motives…, minors…, fields…]`, it invokes the minor on the fields, with each
/// recursive field's hypothesis computed by the **sibling** recursor `I_into.rec` (passed
/// that occurrence's index arguments before the field itself).
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
    let mut field_done: Vec<usize> = Vec::new(); // levels of fields seen so far (index remap)

    let mut args: Vec<Term> = Vec::new();
    for (l, kind) in info.kinds.iter().enumerate() {
        args.push(mk_var(d, field_level(l)));
        if let FieldKind::Rec { into, index_args } = kind {
            // ih = I_into.rec params motives… minors… idx' a_l
            let imgs = ctx_images(d, &field_done, k);
            let idx_imgs: Vec<Term> = index_args.iter().map(|s| s.subst_ctx(&imgs)).collect();
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
            for s in &idx_imgs {
                call = Term::app(call, s.clone()); // indices of the occurrence
            }
            call = Term::app(call, mk_var(d, field_level(l))); // major = the field
            args.push(call);
        }
        field_done.push(field_level(l));
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
