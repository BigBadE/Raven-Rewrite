//! The general inductive elaborator (Phase 2).
//!
//! [`declare_inductive`] takes a high-level [`IndSpec`] — a type former plus its
//! constructor types — and:
//!
//! 1. type-checks the type former and every constructor,
//! 2. enforces **strict positivity** (the inductive may not occur to the left of an
//!    arrow in a field, nor as a non-head argument),
//! 3. *synthesizes* the recursor's type and its per-constructor ι-rules,
//! 4. applies the **large-elimination restriction**: a `Prop`-valued inductive may
//!    only eliminate into a larger universe if it is a subsingleton (≤1 constructor,
//!    all of whose fields are themselves propositions); otherwise its motive is
//!    pinned to `Prop`.
//!
//! The synthesized recursor reproduces the Phase-1 hand-builds of `Nat`/`Eq` exactly
//! (the integration tests check this by re-running the induction proof through the
//! generated declarations).
//!
//! ### Scope
//!
//! Single (non-mutual, non-nested) inductive families with parameters and indices.
//! Recursive constructor arguments must be *direct* (`I params indices`), not under a
//! local binder — i.e. no infinitely-branching / `W`-style arguments (`(B → I) → …`).
//! Such a field is rejected with a clear error rather than mis-elaborated.

use rv_kernel_core::check::{Checker, LocalCtx};
use rv_kernel_core::env::{Constructor, Decl, Env, Inductive, RecRule, Recursor};
use rv_kernel_core::level::Level;
use rv_kernel_core::term::{Grade, Name, Term};
pub(crate) use rv_kernel_core::util::{fold_pis, mk_var, occurs, peel_all_pis, peel_pis};
use std::collections::HashMap;
use std::rc::Rc;

/// Like [`peel_all_pis`], but also records each Π's binder [`Grade`] alongside its
/// domain — needed so a per-field usage grade written on a constructor's `Π` (via
/// [`Term::pi_graded`]) survives being peeled into a field list and can be re-emitted
/// on the corresponding recursor minor-premise binder. Purely additive: fields built
/// with the ordinary ungraded [`Term::pi`] carry `Grade::Many`, so this changes
/// nothing for existing specs.
fn peel_all_pis_graded(mut t: Term) -> (Vec<(Grade, Term)>, Term) {
    let mut doms = Vec::new();
    while let Term::Pi(g, d, b) = t {
        doms.push((g, (*d).clone()));
        t = (*b).clone();
    }
    (doms, t)
}

/// Like [`fold_pis`], but folds each domain back up with its own recorded [`Grade`]
/// (via [`Term::pi_graded`]) instead of always defaulting to `Grade::Many`.
fn fold_pis_graded(doms: &[(Grade, Term)], body: Term) -> Term {
    let mut t = body;
    for (g, d) in doms.iter().rev() {
        t = Term::pi_graded(*g, d.clone(), t);
    }
    t
}

/// A constructor in a high-level inductive specification.
///
/// Per-field usage **grades** are not a separate field of this struct: they are read
/// straight off `ty`'s own `Π`s. A field built with the ordinary [`Term::pi`] carries
/// the default `Grade::Many` (unrestricted, today's behaviour); one built with
/// [`Term::pi_graded`] (e.g. `Grade::One` linear or `Grade::Zero` erased) has that
/// grade **threaded into the synthesized recursor**: the corresponding minor-premise
/// binder for that field is emitted with the same grade, so [`crate::graded`]'s usage
/// pass enforces that a case handler consumes it accordingly (dropped/duplicated
/// linear fields are rejected; a relevantly-used erased field is rejected). This adds
/// no new surface — it just stops [`declare_inductive`] from discarding a grade that
/// was already expressible on `ty` — and is purely additive: ungraded specs (every
/// existing `IndSpec`) synthesize byte-for-byte the same recursor as before.
pub struct CtorSpec {
    pub name: Name,
    /// The constructor's type: `Π params. Π fields. I params indices`.
    pub ty: Term,
}

/// A high-level inductive specification handed to [`declare_inductive`].
pub struct IndSpec {
    pub name: Name,
    /// Universe parameters of the inductive itself (the motive's elimination
    /// universe is added separately by the elaborator).
    pub num_levels: u32,
    /// The type former's type: `Π params. Π indices. Sort _`.
    pub ty: Term,
    pub num_params: usize,
    pub ctors: Vec<CtorSpec>,
    /// Name to give the generated recursor (e.g. `"Nat.rec"`).
    pub rec_name: Name,
}

/// Classification of a constructor field with respect to the inductive `ind`.
enum FieldKind {
    /// The inductive does not occur: an ordinary hypothesis.
    NonRec,
    /// A direct recursive argument `ind params indices`; carries the index args.
    Rec { index_args: Vec<Term> },
}

/// Classify a field type and enforce strict positivity.
fn classify_field(ind: &str, num_params: usize, a: &Term) -> Result<FieldKind, String> {
    if !occurs(ind, a) {
        return Ok(FieldKind::NonRec);
    }
    let (doms, body) = peel_all_pis(a.clone());
    // Strict positivity: the inductive may not occur in any domain to its left.
    for d in &doms {
        if occurs(ind, d) {
            return Err(format!(
                "non-strictly-positive occurrence of '{ind}' (it appears to the left of an arrow)"
            ));
        }
    }
    if !doms.is_empty() {
        return Err(format!(
            "recursive argument of '{ind}' under a local binder (W-type) is not supported"
        ));
    }
    let (head, args) = body.unfold_apps();
    match head {
        Term::Const(m, _) if &*m == ind => {
            if args.len() < num_params {
                return Err(format!("recursive occurrence of '{ind}' is under-applied"));
            }
            Ok(FieldKind::Rec { index_args: args[num_params..].to_vec() })
        }
        _ => Err(format!("'{ind}' occurs in a non-positive position")),
    }
}

/// Images mapping the context `[params p_0..p_{k-1}, fields a_0..a_{l-1}]` (de Bruijn
/// `Var(0)=a_{l-1}`, …, `Var(k+l-1)=p_0`) to recursor variables at depth `d`.
/// `field_levels[t]` is the absolute level of field `a_t`; params are at levels
/// `0..k`.
pub(crate) fn ctx_images(d: usize, field_levels: &[usize], k: usize) -> Vec<Term> {
    let l = field_levels.len();
    let mut images = Vec::with_capacity(k + l);
    // Innermost first: a_{l-1}, a_{l-2}, …, a_0.
    for t in (0..l).rev() {
        images.push(mk_var(d, field_levels[t]));
    }
    // Then params, innermost first: p_{k-1}, …, p_0.
    for t in (0..k).rev() {
        images.push(mk_var(d, t));
    }
    images
}

/// Elaborate and install an inductive family.
pub fn declare_inductive(env: &mut Env, spec: IndSpec) -> Result<(), String> {
    let IndSpec { name, num_levels, ty, num_params, ctors, rec_name } = spec;
    let k = num_params;
    let ind_levels: Vec<Level> = (0..num_levels).map(Level::param).collect();

    // 1. Type-check the type former, and split it into params / indices / result sort.
    {
        let chk = Checker::new(env);
        chk.infer_closed(&ty).map_err(|e| format!("type former '{name}': {e}"))?;
    }
    let (param_doms, after_params) =
        peel_pis(ty.clone(), k).ok_or_else(|| format!("'{name}' has fewer than {k} parameters"))?;
    let (index_doms, result) = peel_all_pis(after_params);
    let m = index_doms.len();
    let result_level = match &result {
        Term::Sort(l) => l.clone(),
        other => return Err(format!("type former '{name}' must end in a sort, found {other:?}")),
    };

    // Install the type former (its recursor name is fixed up front).
    let ctor_names: Vec<Name> = ctors.iter().map(|c| c.name.clone()).collect();
    env.insert(
        name.clone(),
        Decl::Inductive(Rc::new(Inductive {
            num_levels,
            ty: ty.clone(),
            num_params: k,
            num_indices: m,
            ctors: ctor_names.clone(),
            recursor: rec_name.clone(),
            group: vec![name.clone()],
        })),
    )?;

    // 2. Check each constructor: well-typed, strictly positive, and concluding in
    //    `name params …`. Record per-constructor field data for recursor synthesis.
    let mut infos: Vec<CtorInfoLike> = Vec::new();
    for (i, c) in ctors.iter().enumerate() {
        {
            let chk = Checker::new(env);
            chk.infer_closed(&c.ty).map_err(|e| format!("constructor '{}': {e}", c.name))?;
        }
        let (_cparams, rest) = peel_pis(c.ty.clone(), k)
            .ok_or_else(|| format!("constructor '{}' has fewer than {k} parameters", c.name))?;
        let (fields_graded, concl) = peel_all_pis_graded(rest);
        let fields: Vec<Term> = fields_graded.iter().map(|(_, t)| t.clone()).collect();
        let field_grades: Vec<Grade> = fields_graded.iter().map(|(g, _)| *g).collect();
        let (head, cargs) = concl.unfold_apps();
        match head {
            Term::Const(h, _) if h == name => {}
            _ => {
                return Err(format!(
                    "constructor '{}' must conclude in '{name} …', found head {:?}",
                    c.name, concl
                ))
            }
        }
        if cargs.len() < k {
            return Err(format!("constructor '{}' conclusion is under-applied", c.name));
        }
        let concl_index_args = cargs[k..].to_vec();
        let mut kinds = Vec::with_capacity(fields.len());
        for f in &fields {
            kinds.push(classify_field(&name, k, f)?);
        }
        infos.push(CtorInfoLike {
            name: c.name.clone(),
            fields,
            field_grades,
            kinds,
            concl_index_args,
            index: i,
        });
    }

    // Now install the constructors (after positivity passed for all).
    for (i, c) in ctors.iter().enumerate() {
        let num_fields = infos[i].fields.len();
        env.insert(
            c.name.clone(),
            Decl::Constructor(Rc::new(Constructor {
                num_levels,
                ty: c.ty.clone(),
                ind: name.clone(),
                index: i,
                num_fields,
            })),
        )?;
    }

    // 3. Large-elimination restriction. Decide the motive's target universe.
    //    A `Prop` inductive eliminates large-only-if subsingleton.
    let is_prop = matches!(result_level.normalize(), Level::Zero);
    let allow_large = if !is_prop {
        true
    } else {
        is_subsingleton(env, &param_doms, &infos)
    };
    // The recursor gains one extra universe parameter for the motive target unless
    // elimination is pinned to `Prop`.
    let (rec_num_levels, elim_u) = if allow_large {
        (num_levels + 1, Level::param(num_levels))
    } else {
        (num_levels, Level::Zero)
    };

    let big_m = infos.len();

    // Build the recursor type.
    let ind_app = |depth: usize, idx_terms: &[Term]| -> Term {
        let mut t = Term::cnst(name.clone(), ind_levels.clone());
        for j in 0..k {
            t = Term::app(t, mk_var(depth, j));
        }
        for s in idx_terms {
            t = Term::app(t, s.clone());
        }
        t
    };

    // motive domain (at depth k): Π indices. (I params indices) → Sort u
    let motive_dom = {
        let mut inner_doms = index_doms.clone(); // J_l at depths k..k+m-1
        let dmid = k + m;
        let idx_terms: Vec<Term> = (0..m).map(|l| mk_var(dmid, k + l)).collect();
        inner_doms.push(ind_app(dmid, &idx_terms)); // the scrutinee, at depth k+m
        fold_pis(&inner_doms, Term::Sort(elim_u.clone()))
    };

    // minor premises
    let mut minor_doms: Vec<Term> = Vec::with_capacity(big_m);
    for (j, info) in infos.iter().enumerate() {
        let d0 = k + 1 + j;
        minor_doms.push(build_minor(&name, &ind_levels, k, d0, info));
    }

    // top-level index domains: J_l with param refs shifted past motive+minors.
    let top_index_doms: Vec<Term> =
        index_doms.iter().enumerate().map(|(l, j)| j.lift(big_m as isize + 1, l)).collect();

    // major premise (at depth k+1+M+m): I params indices
    let d_major = k + 1 + big_m + m;
    let major_idx: Vec<Term> = (0..m).map(|l| mk_var(d_major, k + 1 + big_m + l)).collect();
    let major_dom = ind_app(d_major, &major_idx);

    // conclusion (at depth k+1+M+m+1): motive indices major
    let d_concl = d_major + 1;
    let concl = {
        let mut t = mk_var(d_concl, k); // motive
        for l in 0..m {
            t = Term::app(t, mk_var(d_concl, k + 1 + big_m + l));
        }
        Term::app(t, mk_var(d_concl, k + 1 + big_m + m)) // major
    };

    // assemble: params, motive, minors, indices, major ⟶ concl
    let mut all_doms = param_doms.clone();
    all_doms.push(motive_dom);
    all_doms.extend(minor_doms);
    all_doms.extend(top_index_doms);
    all_doms.push(major_dom);
    let rec_ty = fold_pis(&all_doms, concl);

    // ι-rules
    let mut rules: HashMap<Name, RecRule> = HashMap::new();
    for info in &infos {
        let rhs = build_rule_rhs(&rec_name, rec_num_levels, k, big_m, info);
        rules.insert(
            info.name.clone(),
            RecRule { ctor: info.name.clone(), num_fields: info.fields.len(), rhs },
        );
    }

    env.insert(
        rec_name.clone(),
        Decl::Recursor(Rc::new(Recursor {
            num_levels: rec_num_levels,
            ty: rec_ty,
            ind: name.clone(),
            num_params: k,
            num_motives: 1,
            num_indices: m,
            num_minors: big_m,
            rules,
        })),
    )?;

    Ok(())
}

/// Build the minor premise for one constructor, at base depth `d0` (the depth just
/// before its first field binder).
fn build_minor(
    ind: &Name,
    ind_levels: &[Level],
    k: usize,
    d0: usize,
    info: &CtorInfoLike,
) -> Term {
    let mut doms: Vec<(Grade, Term)> = Vec::new();
    let mut field_levels: Vec<usize> = Vec::new();
    let mut d = d0;
    for (l, (field_ty, kind)) in info.fields.iter().zip(&info.kinds).enumerate() {
        // The field's own type, re-expressed in the minor context.
        let images = ctx_images(d, &field_levels, k);
        let field_dom = field_ty.subst_ctx(&images);
        // The field's binder carries the grade declared on the constructor's own `Π`
        // for this field (Grade::Many if ungraded) — this is precisely what lets a
        // graded `IndSpec` reject a case handler that drops/duplicates a linear field
        // or relevantly uses an erased one, while leaving every ungraded spec's
        // recursor byte-for-byte unchanged.
        doms.push((info.field_grades[l], field_dom));
        let this_field_level = d;
        field_levels.push(this_field_level);
        d += 1;
        // For a recursive field, an induction hypothesis follows immediately.
        if let FieldKind::Rec { index_args } = kind {
            // ih : motive (index_args') (a_l)   at depth d (after the field binder)
            let imgs = ctx_images(d, &field_levels[..l], k);
            let idx_imgs: Vec<Term> = index_args.iter().map(|s| s.subst_ctx(&imgs)).collect();
            let motive_var = mk_var(d, k);
            let mut ih = motive_var;
            for s in &idx_imgs {
                ih = Term::app(ih, s.clone());
            }
            ih = Term::app(ih, mk_var(d, this_field_level));
            // The induction hypothesis binder is always unrestricted: only the field
            // itself carries a user-declared grade.
            doms.push((Grade::Many, ih));
            d += 1;
        }
        let _ = l;
    }
    // conclusion: motive concl_index_args' (ctor params fields)
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
    let mut body = mk_var(d_mc, k); // motive
    for s in &concl_idx {
        body = Term::app(body, s.clone());
    }
    body = Term::app(body, ctor_app);
    let _ = ind;
    fold_pis_graded(&doms, body)
}

/// Build the ι-rule right-hand side for one constructor: a term to be applied to
/// `[params…, motive, minors…, fields…]`.
fn build_rule_rhs(
    rec_name: &Name,
    rec_num_levels: u32,
    k: usize,
    big_m: usize,
    info: &CtorInfoLike,
) -> Term {
    let n = info.fields.len();
    let d = k + 1 + big_m + n; // body depth (all params/motive/minors/fields bound)
    let rec_levels: Vec<Level> = (0..rec_num_levels).map(Level::param).collect();
    // field a_l is at level k+M+1+l
    let field_level = |l: usize| k + big_m + 1 + l;
    let mut field_done: Vec<usize> = Vec::new(); // levels of fields seen so far (for index remap)

    let mut args: Vec<Term> = Vec::new();
    for (l, kind) in info.kinds.iter().enumerate() {
        // the field value itself
        args.push(mk_var(d, field_level(l)));
        if let FieldKind::Rec { index_args } = kind {
            // ih = rec_name params motive minors index_args' a_l
            let imgs = ctx_images(d, &field_done, k);
            let idx_imgs: Vec<Term> =
                index_args.iter().map(|s| s.subst_ctx(&imgs)).collect();
            let mut call = Term::cnst(rec_name.clone(), rec_levels.clone());
            for j in 0..k {
                call = Term::app(call, mk_var(d, j));
            }
            call = Term::app(call, mk_var(d, k)); // motive
            for j in 0..big_m {
                call = Term::app(call, mk_var(d, k + 1 + j)); // minors
            }
            for s in &idx_imgs {
                call = Term::app(call, s.clone());
            }
            call = Term::app(call, mk_var(d, field_level(l))); // major = a_l
            args.push(call);
        }
        field_done.push(field_level(l));
    }
    // q_j is the minor at level k+1+j
    let mut body = mk_var(d, k + 1 + info.index);
    for a in args {
        body = Term::app(body, a);
    }
    // wrap in λ over [params, motive, minors, fields]
    let mut t = body;
    for _ in 0..d {
        t = Term::lam(Term::prop(), t);
    }
    t
}

/// Is a `Prop` inductive a subsingleton (so large elimination is sound)? True when it
/// has no constructors (`False`-like, `ex falso` into anything) or exactly one
/// constructor all of whose fields are themselves propositions.
fn is_subsingleton(env: &Env, param_doms: &[Term], infos: &[CtorInfoLike]) -> bool {
    match infos.len() {
        0 => true, // empty (`False`-like): ex falso eliminates into any universe
        1 => {
            // Single constructor: large elimination is sound iff every field is a
            // *proof* — i.e. its type lives in `Prop`. Sort-check each field in the
            // real telescope context [params, prior fields].
            let chk = Checker::new(env);
            let mut ctx = LocalCtx::new();
            for p in param_doms {
                ctx.push(p.clone());
            }
            for f in &infos[0].fields {
                match chk.infer_sort(&mut ctx, f) {
                    Ok(l) if matches!(l.normalize(), Level::Zero) => ctx.push(f.clone()),
                    _ => return false, // a data field (or un-sortable): restrict
                }
            }
            true
        }
        _ => false,
    }
}

/// Per-constructor data threaded from checking into recursor/ι-rule synthesis.
struct CtorInfoLike {
    name: Name,
    fields: Vec<Term>,
    /// Per-field usage grade, read off the constructor's own `Π`s (`Grade::Many` if
    /// the field was built with the ordinary ungraded [`Term::pi`]). Threaded onto
    /// the corresponding recursor minor-premise binder in [`build_minor`].
    field_grades: Vec<Grade>,
    kinds: Vec<FieldKind>,
    concl_index_args: Vec<Term>,
    index: usize,
}

// ---------------------------------------------------------------------------
// Convenience spec builders for the standard inductives (also used by tests).
// ---------------------------------------------------------------------------

use rv_kernel_core::term::name;

fn cn(s: &str) -> Term {
    Term::cnst(name(s), vec![])
}

/// `Nat : Type 0` with `Nat.zero`, `Nat.succ`.
pub fn nat_spec() -> IndSpec {
    IndSpec {
        name: name("Nat"),
        num_levels: 0,
        ty: Term::typ(0),
        num_params: 0,
        ctors: vec![
            CtorSpec { name: name("Nat.zero"), ty: cn("Nat") },
            CtorSpec { name: name("Nat.succ"), ty: Term::arrow(cn("Nat"), cn("Nat")) },
        ],
        rec_name: name("Nat.rec"),
    }
}

/// `Eq.{u} : Π (A : Sort u) (a : A), A → Prop` with `Eq.refl`.
pub fn eq_spec() -> IndSpec {
    let u = Level::param(0);
    IndSpec {
        name: name("Eq"),
        num_levels: 1,
        ty: Term::pi(
            Term::Sort(u.clone()),
            Term::pi(Term::Var(0), Term::pi(Term::Var(1), Term::prop())),
        ),
        num_params: 2,
        ctors: vec![CtorSpec {
            name: name("Eq.refl"),
            ty: Term::pi(
                Term::Sort(u.clone()),
                Term::pi(
                    Term::Var(0),
                    Term::apps(
                        Term::cnst(name("Eq"), vec![u]),
                        [Term::Var(1), Term::Var(0), Term::Var(0)],
                    ),
                ),
            ),
        }],
        rec_name: name("Eq.rec"),
    }
}

/// `Bool : Type 0` with `Bool.false`, `Bool.true`.
pub fn bool_spec() -> IndSpec {
    IndSpec {
        name: name("Bool"),
        num_levels: 0,
        ty: Term::typ(0),
        num_params: 0,
        ctors: vec![
            CtorSpec { name: name("Bool.false"), ty: cn("Bool") },
            CtorSpec { name: name("Bool.true"), ty: cn("Bool") },
        ],
        rec_name: name("Bool.rec"),
    }
}

/// `List : Type 0 → Type 0` with `List.nil`, `List.cons` (a recursive field).
pub fn list_spec() -> IndSpec {
    let list_a = |a: Term| Term::app(cn("List"), a);
    IndSpec {
        name: name("List"),
        num_levels: 0,
        ty: Term::pi(Term::typ(0), Term::typ(0)),
        num_params: 1,
        ctors: vec![
            CtorSpec { name: name("List.nil"), ty: Term::pi(Term::typ(0), list_a(Term::Var(0))) },
            CtorSpec {
                name: name("List.cons"),
                // Π (A:Type0) (head:A) (tail:List A). List A
                ty: Term::pi(
                    Term::typ(0),
                    Term::pi(
                        Term::Var(0),
                        Term::pi(list_a(Term::Var(1)), list_a(Term::Var(2))),
                    ),
                ),
            },
        ],
        rec_name: name("List.rec"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_kernel_core::reduce::Reducer;

    fn lit(n: u32) -> Term {
        let mut t = cn("Nat.zero");
        for _ in 0..n {
            t = Term::app(cn("Nat.succ"), t);
        }
        t
    }

    /// The generated `Nat`/`Eq` recursors are good enough to carry the real Phase-1
    /// induction proof of `∀ n, add n 0 = n` — the generator reproduces the
    /// hand-builds behaviourally.
    #[test]
    fn generated_nat_eq_support_induction() {
        let mut env = Env::new();
        declare_inductive(&mut env, nat_spec()).unwrap();
        declare_inductive(&mut env, eq_spec()).unwrap();

        // Computation still works: 2 + 3 = 5.
        let r = Reducer::new(&env);
        let add = |m: Term, n: Term| {
            Term::apps(
                Term::cnst(name("Nat.rec"), vec![Level::of_nat(1)]),
                [
                    Term::lam(cn("Nat"), cn("Nat")),
                    n,
                    Term::lam(cn("Nat"), Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0)))),
                    m,
                ],
            )
        };
        assert!(r.is_def_eq(&add(lit(2), lit(3)), &lit(5)));

        // The induction proof type-checks against the *generated* declarations.
        let (proof, goal) = rv_kernel_core::inductive::add_n_zero_proof();
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&proof).expect("induction proof should check");
        assert!(r.is_def_eq(&ty, &goal), "got {ty:?}");
    }

    /// A generated `Bool` recursor computes: `Bool.rec _ f t true ↦ t`.
    #[test]
    fn generated_bool_eliminates() {
        let mut env = Env::new();
        declare_inductive(&mut env, bool_spec()).unwrap();
        let r = Reducer::new(&env);
        // Bool.rec.{1} (λ_.Bool) Bool.false Bool.true Bool.true  ↦  Bool.true
        let elim = |scrut: Term| {
            Term::apps(
                Term::cnst(name("Bool.rec"), vec![Level::of_nat(1)]),
                [Term::lam(cn("Bool"), cn("Bool")), cn("Bool.false"), cn("Bool.true"), scrut],
            )
        };
        assert!(r.is_def_eq(&elim(cn("Bool.true")), &cn("Bool.true")));
        assert!(r.is_def_eq(&elim(cn("Bool.false")), &cn("Bool.false")));
    }

    /// A generated recursor with a *recursive* field (`List.cons`) computes through
    /// its induction hypothesis: `length [0,0] = 2`.
    #[test]
    fn generated_list_recursion_computes() {
        let mut env = Env::new();
        declare_inductive(&mut env, nat_spec()).unwrap();
        declare_inductive(&mut env, list_spec()).unwrap();
        // Sanity: the recursor type is well-formed.
        let chk = Checker::new(&env);
        chk.infer_closed(env.get("List.rec").unwrap().ty()).unwrap();

        let nat = || cn("Nat");
        let nil = Term::app(cn("List.nil"), nat());
        let cons = |h: Term, t: Term| Term::apps(cn("List.cons"), [nat(), h, t]);
        let list2 = cons(lit(0), cons(lit(0), nil)); // [0, 0]

        // length = List.rec.{1} Nat (λ_.Nat) zero (λ head tail ih. succ ih)
        // List.rec args: A, motive, nil_case, cons_case, scrutinee
        let length = |xs: Term| {
            Term::apps(
                Term::cnst(name("List.rec"), vec![Level::of_nat(1)]),
                [
                    nat(),                                   // A (param)
                    Term::lam(Term::app(cn("List"), nat()), nat()), // motive : List Nat → Nat
                    cn("Nat.zero"),                          // nil case
                    // cons case: λ (head:Nat) (tail:List Nat) (ih:Nat). succ ih
                    Term::lam(
                        nat(),
                        Term::lam(
                            Term::app(cn("List"), nat()),
                            Term::lam(nat(), Term::app(cn("Nat.succ"), Term::Var(0))),
                        ),
                    ),
                    xs,
                ],
            )
        };
        let r = Reducer::new(&env);
        assert!(r.is_def_eq(&length(list2), &lit(2)), "length [0,0] should be 2");
    }

    /// Strict positivity is enforced: `Bad.mk : (Bad → Bad) → Bad` is rejected.
    #[test]
    fn non_strictly_positive_rejected() {
        let mut env = Env::new();
        let spec = IndSpec {
            name: name("Bad"),
            num_levels: 0,
            ty: Term::typ(0),
            num_params: 0,
            ctors: vec![CtorSpec {
                name: name("Bad.mk"),
                ty: Term::arrow(Term::arrow(cn("Bad"), cn("Bad")), cn("Bad")),
            }],
            rec_name: name("Bad.rec"),
        };
        let err = declare_inductive(&mut env, spec).unwrap_err();
        assert!(err.contains("positive"), "unexpected error: {err}");
    }

    /// The `Prop` large-elimination restriction: a multi-constructor `Prop` (`Or`)
    /// gets a `Prop`-pinned recursor (no extra universe param), while a subsingleton
    /// `Prop` (`And`, one constructor, all-proof fields) keeps large elimination.
    #[test]
    fn prop_large_elimination_restriction() {
        // Or : Prop → Prop → Prop with inl/inr.
        let or_app = |a: Term, b: Term| Term::apps(cn("Or"), [a, b]);
        let or_spec = IndSpec {
            name: name("Or"),
            num_levels: 0,
            ty: Term::pi(Term::prop(), Term::pi(Term::prop(), Term::prop())),
            num_params: 2,
            ctors: vec![
                CtorSpec {
                    name: name("Or.inl"),
                    ty: Term::pi(
                        Term::prop(),
                        Term::pi(
                            Term::prop(),
                            Term::pi(Term::Var(1), or_app(Term::Var(2), Term::Var(1))),
                        ),
                    ),
                },
                CtorSpec {
                    name: name("Or.inr"),
                    ty: Term::pi(
                        Term::prop(),
                        Term::pi(
                            Term::prop(),
                            Term::pi(Term::Var(0), or_app(Term::Var(2), Term::Var(1))),
                        ),
                    ),
                },
            ],
            rec_name: name("Or.rec"),
        };
        let mut env = Env::new();
        declare_inductive(&mut env, or_spec).unwrap();
        // Restricted: recursor has NO extra elimination universe parameter.
        assert_eq!(env.get("Or.rec").unwrap().num_levels(), 0);

        // And : Prop → Prop → Prop with one constructor `intro : A → B → And A B`.
        let and_app = |a: Term, b: Term| Term::apps(cn("And"), [a, b]);
        let and_spec = IndSpec {
            name: name("And"),
            num_levels: 0,
            ty: Term::pi(Term::prop(), Term::pi(Term::prop(), Term::prop())),
            num_params: 2,
            ctors: vec![CtorSpec {
                name: name("And.intro"),
                ty: Term::pi(
                    Term::prop(),
                    Term::pi(
                        Term::prop(),
                        // Π (_:A) (_:B). And A B
                        Term::pi(
                            Term::Var(1),
                            Term::pi(Term::Var(1), and_app(Term::Var(3), Term::Var(2))),
                        ),
                    ),
                ),
            }],
            rec_name: name("And.rec"),
        };
        let mut env2 = Env::new();
        declare_inductive(&mut env2, and_spec).unwrap();
        // Subsingleton: large elimination kept (one extra universe parameter).
        assert_eq!(env2.get("And.rec").unwrap().num_levels(), 1);
    }
}
