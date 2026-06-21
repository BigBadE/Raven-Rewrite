//! Code-first verification: the Rust-like `fn … requires … ensures …` surface, on
//! top of the dependent kernel.
//!
//! A [`Session`] wraps a [`Kernel`] and adds the engineer-facing layer. Specs are
//! written as **inline ghost calls** in the body:
//!
//! ```text
//! fn f (x : T) -> R {
//!     requires(P);
//!     ensures(Q);     // `result` refers to the returned value
//!     body
//! }
//! ```
//!
//! Declaring it does two things:
//! 1. installs `f := λ x. body` as a checked kernel **definition**, and
//! 2. generates the correctness **obligation** as a kernel proposition
//!    `∀ x, P → Q[result := f x]` — an *open goal*, **not** an axiom.
//!
//! When a `fn` is declared the session first tries to discharge its obligation
//! **automatically** with a built-in reflexivity/conversion tactic (no SMT, no AI):
//! many specs — `ensures result == <something the body computes to>` — are
//! *definitionally* true, and the kernel's NbE conversion closes them outright. What's
//! left is reported as an open goal, to be discharged by a hand proof (`prove f := …`)
//! or a supplied proof term ([`Session::prove_with`], the injection point for a future
//! SMT/AI back-end). The kernel checks every discharge, automatic or not, so nothing
//! unsound can slip through. This is the "Rust usability + Lean-core power"
//! combination: the obligation lives in the full dependent logic, but the user writes
//! only the spec.

use crate::check::{Checker, LocalCtx};
use crate::elab::run_command;
use crate::elab2::{params_mask, rewrite_rec_calls, BundleMember, Implicits, Infer, RecInfo};
use crate::generate::peel_all_pis;
use crate::kernel::Kernel;
use crate::level::Level;
use crate::reduce::Reducer;
use crate::surface::{self, Binder, Command, Expr, MatchArm};
use crate::term::{name, Term};
use std::collections::HashMap;

/// A verification session: a kernel plus the open obligations of declared `fn`s.
///
/// Commands run through the **inferring** elaborator ([`crate::elab2`]): `def`/`fn`
/// bodies, specs, and proofs get type inference, holes (`_`), implicit-argument
/// auto-insertion, and universe-level inference. (`axiom`/`inductive` — purely
/// type-level and fully explicit — still go through the core explicit elaborator, but
/// the session records which of their parameters are implicit so call sites elsewhere
/// auto-insert them.)
#[derive(Default)]
pub struct Session {
    pub k: Kernel,
    /// `fn` name → (its universe params, its correctness obligation).
    goals: HashMap<String, (Vec<String>, Term)>,
    /// Per-name implicit-argument masks, consulted by the inferring elaborator.
    implicits: Implicits,
    /// Type-class instance registry: class head name → instance definition names, consulted
    /// by the elaborator's instance resolution (filling class-typed implicit holes).
    instances: HashMap<String, Vec<String>>,
    /// The source of the program currently being run, so the elaborator can render a caret
    /// under the offending sub-term of a type error (the byte spans in `Expr::Spanned` index
    /// into this string).
    cur_src: String,
}

impl Session {
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse and run a program (commands plus `fn`/`prove`).
    ///
    /// Recursive functions are detected and compiled automatically: a `fn` that matches
    /// on a parameter of a *single* inductive may call itself by name (structural
    /// recursion); a contiguous run of `fn`s over the members of a *mutual* inductive
    /// group is recognised as a mutually-recursive bundle and compiled jointly — no
    /// `mutual { … }` block or hand-written recursor needed.
    pub fn run(&mut self, src: &str) -> Result<(), String> {
        self.cur_src = src.to_string();
        let cmds = surface::parse_program_spanned(src)?;
        let mut pending: Vec<Command> = Vec::new();
        let mut pending_group: Option<Vec<String>> = None;
        let mut group_loc = String::new();
        for (cmd, (line, col)) in cmds {
            let loc = format!("{line}:{col}");
            if matches!(cmd, Command::Fn { .. }) {
                if let Some(group) = self.recursion_group_of(&cmd)? {
                    // A member of a mutual group: buffer until the group is complete.
                    if pending_group.as_ref() != Some(&group) {
                        if !pending.is_empty() {
                            return Err("mutual function groups must be written contiguously".into());
                        }
                        pending_group = Some(group.clone());
                        group_loc = loc.clone();
                    }
                    pending.push(cmd);
                    if pending.len() == group.len() {
                        let members = std::mem::take(&mut pending);
                        pending_group = None;
                        let gl = group_loc.clone();
                        self.compile_bundle(members, &group).map_err(|e| {
                            format!("{gl}: in mutual fn group {{{}}}: {e}", group.join(", "))
                        })?;
                    }
                    continue;
                }
                let label = cmd_label(&cmd);
                self.run_solo_fn(cmd).map_err(|e| format!("{loc}: in {label}: {e}"))?;
                continue;
            }
            if !pending.is_empty() {
                return Err("a mutual function group must be contiguous".into());
            }
            self.run_command(&cmd)
                .map_err(|e| format!("{loc}: in {}: {e}", cmd_label(&cmd)))?;
        }
        if !pending.is_empty() {
            return Err("incomplete mutual function group (a sibling function is missing)".into());
        }
        Ok(())
    }

    /// If `cmd` is a `fn` that recurses on a parameter of a **mutual** inductive group,
    /// return that group's member names (in declaration order); else `None`.
    fn recursion_group_of(&self, cmd: &Command) -> Result<Option<Vec<String>>, String> {
        let Command::Fn { params, body, .. } = cmd else { return Ok(None) };
        let Some((_, _, scrut_name)) = match_recursion(params, body) else { return Ok(None) };
        // Find and elaborate the matched parameter's type, with earlier params in scope.
        let mut inf = Infer::with_implicits(self.k.env(), &self.implicits).with_src(&self.cur_src);
        for b in params {
            for n in &b.names {
                if n == &scrut_name {
                    let (raw, _) = inf.infer(&b.ty)?;
                    let ty = inf.finish(&raw)?;
                    let (head, _) =
                        crate::reduce::Reducer::new(self.k.env()).whnf(&ty).unfold_apps();
                    if let Term::Const(ind, _) = head {
                        if let Some(crate::env::Decl::Inductive(i)) = self.k.env().get(&ind) {
                            if i.group.len() > 1 {
                                return Ok(Some(i.group.iter().map(|x| x.to_string()).collect()));
                            }
                        }
                    }
                    return Ok(None);
                }
                let (raw, _) = inf.infer(&b.ty)?;
                let ty = inf.finish(&raw)?;
                inf.push_local(n, ty);
            }
        }
        Ok(None)
    }

    /// Run a solo `fn`, rewriting any self-recursive name-calls into the `match` IH.
    fn run_solo_fn(&mut self, cmd: Command) -> Result<(), String> {
        let Command::Fn { name: nm, levels, params, ret, requires, ensures, body } = cmd else {
            unreachable!()
        };
        let body = match match_recursion(&params, &body) {
            Some((spos, pnames, _)) => {
                let mut recs = RecInfo::new();
                recs.insert(nm.clone(), (spos, pnames));
                rewrite_rec_calls(&body, &recs)
            }
            None => body,
        };
        self.declare_fn(&nm, &levels, &params, &ret, &requires, &ensures, &body)
    }

    /// Compile a contiguous bundle of mutually-recursive `fn`s (one per group member).
    fn compile_bundle(&mut self, cmds: Vec<Command>, group: &[String]) -> Result<(), String> {
        // Build the recursion map (each member's matched-arg position + param names) so
        // sibling/self calls in every body can be rewritten to the `.rec` hypotheses.
        let mut recs = RecInfo::new();
        for c in &cmds {
            let Command::Fn { name: nm, params, body, .. } = c else { unreachable!() };
            let (spos, pnames, _) = match_recursion(params, body)
                .ok_or("a mutual function must be a `match` on one of its parameters")?;
            if params.iter().map(|b| b.names.len()).sum::<usize>() != 1 {
                return Err(format!(
                    "mutual function '{nm}' must take exactly its scrutinee (extra parameters \
                     in a mutual bundle are not yet supported)"
                ));
            }
            recs.insert(nm.clone(), (spos, pnames));
        }
        // Order members by the inductive group, rewriting each body's recursive calls.
        let mut members: Vec<Option<BundleMember>> = (0..group.len()).map(|_| None).collect();
        for c in &cmds {
            let Command::Fn { name: nm, params, ret, body, .. } = c else { unreachable!() };
            let (_, _, scrut_name) = match_recursion(params, body).unwrap();
            let scrut_ty = param_type(params, &scrut_name).unwrap().clone();
            let Expr::Match(_, arms) = body.peel() else { unreachable!() };
            let arms: Vec<MatchArm> = arms
                .iter()
                .map(|a| MatchArm {
                    pat: a.pat.clone(),
                    body: rewrite_rec_calls(&a.body, &recs),
                })
                .collect();
            let idx = self.member_index(&scrut_ty, group)?;
            if members[idx].is_some() {
                return Err(format!("two functions recurse on group member {}", group[idx]));
            }
            members[idx] = Some(BundleMember {
                def_name: nm.clone(),
                scrut_name,
                scrut_ty,
                ret: ret.clone(),
                arms,
            });
        }
        let members: Vec<BundleMember> = members
            .into_iter()
            .collect::<Option<_>>()
            .ok_or("mutual bundle does not cover every group member")?;

        let defs = {
            let mut inf = Infer::with_implicits(self.k.env(), &self.implicits).with_src(&self.cur_src);
            inf.compile_bundle(&members, group)?
        };
        for (nm, ty, value) in defs {
            self.k.add_definition(&nm, 0, ty, value)?;
            self.implicits.insert(nm, vec![false]); // single scrutinee param
        }
        Ok(())
    }

    /// Which group member's type does `scrut_ty` recurse on?
    fn member_index(&self, scrut_ty: &Expr, group: &[String]) -> Result<usize, String> {
        let mut inf = Infer::with_implicits(self.k.env(), &self.implicits).with_src(&self.cur_src);
        let (raw, _) = inf.infer(scrut_ty)?;
        let ty = inf.finish(&raw)?;
        let (head, _) = crate::nbe::Nbe::new(self.k.env()).normalize(&ty).unfold_apps();
        if let Term::Const(ind, _) = head {
            if let Some(i) = group.iter().position(|g| *g == *ind) {
                return Ok(i);
            }
        }
        Err("mutual function does not recurse on a group member".into())
    }

    fn run_command(&mut self, cmd: &Command) -> Result<(), String> {
        match cmd {
            Command::Fn { name, levels, params, ret, requires, ensures, body } => {
                self.declare_fn(name, levels, params, ret, requires, ensures, body)
            }
            Command::Prove { name, proof } => {
                let (levels, goal) = self.goal_entry(name)?;
                let proof_term = {
                    let mut inf = Infer::with_implicits(self.k.env(), &self.implicits).with_src(&self.cur_src)
                        .with_levels(&levels)
                        .with_instances(&self.instances);
                    let t = inf.check(proof, &goal)?;
                    inf.resolve_instances()?;
                    inf.finish(&t)?
                };
                self.discharge(name, proof_term)
            }
            Command::Def { name, levels, params, ty, body } => {
                self.install_definition(name, levels, params, ty, body)
            }
            Command::Class(name) => {
                // Mark `name` as a class (an empty instance set), so resolution can give a
                // precise "no instance found" even before any instance is declared.
                self.instances.entry(name.clone()).or_default();
                Ok(())
            }
            Command::Instance { name, levels, params, ty, body } => {
                self.install_definition(name, levels, params, ty, body)?;
                // Register under the class = the head of the instance's result type.
                if let Some(class) = expr_head_name(ty) {
                    self.instances.entry(class).or_default().push(name.clone());
                    Ok(())
                } else {
                    Err(format!(
                        "instance '{name}': could not determine the class (its type must be \
                         `Class args…`)"
                    ))
                }
            }
            Command::Check(e) => {
                let t = {
                    let mut inf = Infer::with_implicits(self.k.env(), &self.implicits).with_src(&self.cur_src);
                    let (t, _) = inf.infer(e)?;
                    inf.finish(&t)?
                };
                self.k.infer(&t).map(|_| ())
            }
            Command::Axiom { name, params, .. } => {
                run_command(&mut self.k, cmd)?;
                self.implicits.insert(name.clone(), params_mask(params));
                Ok(())
            }
            Command::Inductive { name, params, ctors, .. } => {
                run_command(&mut self.k, cmd)?;
                self.record_inductive_implicits(name, params, ctors);
                Ok(())
            }
            Command::Mutual(members) => {
                run_command(&mut self.k, cmd)?;
                for m in members {
                    if let Command::Inductive { name, params, ctors, .. } = m {
                        self.record_inductive_implicits(name, params, ctors);
                    }
                }
                Ok(())
            }
        }
    }

    /// Record the implicit-argument masks for an inductive's type former and each of its
    /// constructors (constructors inherit the inductive's parameter implicitness).
    fn record_inductive_implicits(&mut self, name: &str, params: &[Binder], ctors: &[(String, Expr)]) {
        let mask = params_mask(params);
        self.implicits.insert(name.to_string(), mask.clone());
        for (cname, _) in ctors {
            let q = if cname.contains('.') { cname.clone() } else { format!("{name}.{cname}") };
            self.implicits.insert(q, mask.clone());
        }
    }

    /// Install a checked definition `nm := λ params. body : Π params. ret`, elaborated
    /// with inference (the body is *checked against* the declared return type so
    /// inference flows inward), and record its implicit mask.
    fn install_definition(
        &mut self,
        nm: &str,
        levels: &[String],
        params: &[Binder],
        ret: &Expr,
        body: &Expr,
    ) -> Result<(), String> {
        let (tty, tbody) = {
            let mut inf = Infer::with_implicits(self.k.env(), &self.implicits).with_src(&self.cur_src)
                .with_levels(levels)
                .with_instances(&self.instances);
            let doms = inf.push_params(params)?;
            let (ret_t, _) = inf.infer(ret)?;
            let body_t = inf.check(body, &ret_t)?;
            inf.resolve_instances()?;
            for _ in 0..doms.len() {
                inf.pop_local();
            }
            let mut full_ty = ret_t;
            let mut full_body = body_t;
            for d in doms.iter().rev() {
                full_ty = Term::pi(d.clone(), full_ty);
                full_body = Term::lam(d.clone(), full_body);
            }
            (inf.finish(&full_ty)?, inf.finish(&full_body)?)
        };
        self.k.add_definition(nm, levels.len() as u32, tty, tbody)?;
        self.implicits.insert(nm.to_string(), params_mask(params));
        Ok(())
    }

    /// The obligation of `fn name`, if it has one (a spec with an `ensures`).
    pub fn goal(&self, name: &str) -> Option<&Term> {
        self.goals.get(name).map(|(_, g)| g)
    }

    /// Whether `fn name`'s obligation has been discharged.
    pub fn verified(&self, name: &str) -> bool {
        self.k.env().contains(&format!("{name}.proof"))
    }

    fn goal_entry(&self, name: &str) -> Result<(Vec<String>, Term), String> {
        self.goals
            .get(name)
            .cloned()
            .ok_or_else(|| format!("no open obligation named '{name}'"))
    }

    /// Discharge `fn name`'s obligation with an explicit proof *term* — the injection
    /// point for an automated (SMT/AI) back-end. The kernel checks `proof : goal`.
    pub fn prove_with(&mut self, name: &str, proof: Term) -> Result<(), String> {
        self.discharge(name, proof)
    }

    fn discharge(&mut self, name: &str, proof: Term) -> Result<(), String> {
        let (levels, goal) = self.goal_entry(name)?;
        self.k
            .add_definition(&format!("{name}.proof"), levels.len() as u32, goal, proof)
            .map_err(|e| format!("proof of '{name}' rejected: {e}"))
    }

    #[allow(clippy::too_many_arguments)]
    fn declare_fn(
        &mut self,
        nm: &str,
        levels: &[String],
        params: &[Binder],
        ret: &Expr,
        requires: &[Expr],
        ensures: &[Expr],
        body: &Expr,
    ) -> Result<(), String> {
        // 1. Install the function definition `nm := λ params. body : Π params. ret`.
        self.install_definition(nm, levels, params, ret, body)?;

        // 2. Build the obligation `∀ params, requires… → ensures…[result := nm params]`.
        if ensures.is_empty() {
            return Ok(()); // no postcondition ⇒ nothing to prove
        }
        let np = params.iter().map(|b| b.names.len()).sum::<usize>();
        // The obligation is built with the inferring elaborator too (so specs can use
        // holes, implicit args, and `==`). Each elaborated piece is **zonked
        // immediately** to a metavariable-free core term, *before* the de Bruijn
        // surgery (lifting preconditions, substituting `result`) — so no unsolved hole
        // is ever lifted, keeping indices correct.
        let obligation = {
            let mut e =
                Infer::with_implicits(self.k.env(), &self.implicits).with_src(&self.cur_src).with_levels(levels);

            // Push the parameters, collecting their (zonked) domains for the Π.
            let mut param_doms = Vec::new();
            for b in params {
                for n in &b.names {
                    let (raw, _) = e.infer(&b.ty)?;
                    let ty = e.finish(&raw)?;
                    param_doms.push(ty.clone());
                    e.push_local(n, ty);
                }
            }
            // The return type, then `result : R` as the innermost binder.
            let (ret_raw, _) = e.infer(ret)?;
            let ret_ty = e.finish(&ret_raw)?;
            e.push_local("result", ret_ty);
            // Elaborate each `ensures` under [params, result] and conjoin them with `And`.
            let (q0, _) = e.infer(&ensures[0])?;
            let mut q = e.finish(&q0)?;
            for extra in &ensures[1..] {
                let (qi, _) = e.infer(extra)?;
                let qi = e.finish(&qi)?;
                q = Term::apps(Term::cnst(name("And"), vec![]), [q, qi]);
            }
            e.pop_local(); // drop `result`

            // result := nm.{levels} param0 … param_{np-1}
            let level_args = (0..levels.len() as u32).map(Level::param).collect();
            let mut result_val = Term::cnst(name(nm), level_args);
            for i in 0..np {
                result_val = Term::app(result_val, Term::Var(np - 1 - i));
            }
            // Substitute `result` (the innermost binder, Var 0) by `nm params`.
            let q_sub = q.instantiate(&result_val);

            // Preconditions become a chain of implications `P1 → P2 → … → Q`, all under
            // [params]. Elaborate+zonk them, then fold from the inside out (lifting).
            let mut pre_terms = Vec::new();
            for p in requires {
                let (pt, _) = e.infer(p)?;
                pre_terms.push(e.finish(&pt)?);
            }
            let mut body_obl = q_sub;
            for p in pre_terms.into_iter().rev() {
                body_obl = Term::pi(p, body_obl.lift(1, 0));
            }
            for _ in 0..np {
                e.pop_local();
            }

            // ∀ params. body_obl
            let mut obligation = body_obl;
            for dom in param_doms.into_iter().rev() {
                obligation = Term::pi(dom, obligation);
            }
            obligation
        };

        // Sanity: the obligation must be a well-formed proposition.
        self.k
            .infer(&obligation)
            .map_err(|err| format!("obligation for '{nm}' is ill-formed: {err}"))?;
        self.goals.insert(nm.to_string(), (levels.to_vec(), obligation));
        // Try to prove it automatically (rfl / conversion). Failure just leaves it open.
        self.auto_discharge(nm);
        Ok(())
    }

    /// Attempt to discharge `fn name`'s obligation with the built-in tactic. Returns
    /// whether it succeeded. Never errors — an obligation it can't close stays open.
    pub fn auto_discharge(&mut self, name: &str) -> bool {
        if self.verified(name) {
            return true;
        }
        let Some((_, obligation)) = self.goals.get(name).cloned() else {
            return false;
        };
        // Cheap structural search first; induction (heavier) only as a fallback.
        let proof = try_rfl(&self.k, &obligation).or_else(|| try_induction(&self.k, &obligation));
        if let Some(proof) = proof {
            return self.discharge(name, proof).is_ok();
        }
        false
    }

    /// Names of `fn`s whose obligations are discharged.
    pub fn verified_fns(&self) -> Vec<String> {
        let mut v: Vec<_> = self.goals.keys().filter(|n| self.verified(n)).cloned().collect();
        v.sort();
        v
    }

    /// Names of `fn`s whose obligations are still open.
    pub fn open_fns(&self) -> Vec<String> {
        let mut v: Vec<_> = self.goals.keys().filter(|n| !self.verified(n)).cloned().collect();
        v.sort();
        v
    }

    /// Are all declared `fn`s verified?
    pub fn all_verified(&self) -> bool {
        self.open_fns().is_empty()
    }

    /// **Evaluate** a (parameterless) definition to its canonical value by normalising
    /// it with NbE, then render it. This is the kernel surface's *execution* path:
    /// `fn main() -> Nat { … }` installs `main : Nat := …`, and `eval("main")` computes
    /// it to a numeral / constructor tree. Errors if the name isn't an evaluable `Def`.
    pub fn eval(&self, name: &str) -> Result<Term, String> {
        let value = match self.k.env().get(name) {
            Some(crate::env::Decl::Def { value, .. }) => value.clone(),
            Some(_) => return Err(format!("'{name}' is not an evaluable definition")),
            None => return Err(format!("no definition named '{name}'")),
        };
        Ok(crate::nbe::Nbe::new(self.k.env()).normalize(&value))
    }

    /// Evaluate `name` and render the result as a readable string (`Nat` literals as
    /// numbers, other data as a constructor tree).
    pub fn run_entry(&self, name: &str) -> Result<String, String> {
        Ok(render(self.k.env(), &self.eval(name)?))
    }

    /// A one-line-per-function status report.
    pub fn report(&self) -> String {
        let mut names: Vec<_> = self.goals.keys().cloned().collect();
        names.sort();
        names
            .into_iter()
            .map(|n| {
                let status = if self.verified(&n) { "verified" } else { "OPEN" };
                format!("{n}: {status}")
            })
            .collect::<Vec<_>>()
            .join("\n")
    }
}

/// The built-in proof search: discharge an obligation by a bounded set of *sound* moves
/// (every result is re-checked by the kernel, so the search is untrusted). Intros the
/// `∀`/`→` binders — turning preconditions into **hypotheses** — then tries to close the
/// remaining goal with [`prove_leaf`]. Returns a proof term, or `None` (then it stays an
/// open goal for a hand proof / future SMT back-end).
fn try_rfl(k: &Kernel, obligation: &Term) -> Option<Term> {
    // Intro all leading binders, recording their domains (which become hypotheses).
    let mut doms = Vec::new();
    let mut leaf = obligation.clone();
    while let Term::Pi(_, d, b) = leaf {
        doms.push((*d).clone());
        leaf = (*b).clone();
    }
    let leaf_proof = prove_leaf(k, &doms, &leaf)?;
    // Wrap it back up in λs matching the intro'd binders.
    let mut proof = leaf_proof;
    for d in doms.into_iter().rev() {
        proof = Term::lam(d, proof);
    }
    // Final check against the obligation (cheap insurance; discharge re-checks too).
    k.check(&proof, obligation).is_ok().then_some(proof)
}

/// **Induction tactic.** When the obligation is `∀ (x : I …), G` and `I` is a single,
/// non-indexed inductive, prove it by applying `I`'s recursor with motive `λ x. G`: each
/// constructor becomes a subgoal `G[x := C fields]` with the fields and their **induction
/// hypotheses** in scope, discharged by the leaf prover. This is what closes proofs by
/// cases / structural induction (e.g. `∀ b : Bool, b = true ∨ b = false`) automatically.
/// The assembled term is kernel-checked, so an unsound assembly is simply rejected.
fn try_induction(k: &Kernel, obligation: &Term) -> Option<Term> {
    use crate::env::Decl;
    let Term::Pi(_, dom, body) = obligation else { return None };
    let r = Reducer::new(k.env());
    let (head, params) = r.whnf(dom).unfold_apps();
    let Term::Const(ind_name, ls) = &head else { return None };
    let Some(Decl::Inductive(ind)) = k.env().get(ind_name) else { return None };
    if ind.group.len() > 1 || ind.num_indices != 0 {
        return None; // single, non-indexed inductives only
    }
    let ind = ind.clone();
    let Some(Decl::Recursor(rec)) = k.env().get(&ind.recursor) else { return None };
    let rec = rec.clone();

    // Motive `λ (x : dom). G` (the obligation body is already in the `x` context), and
    // recursor level args eliminating into `Prop` (the obligation is a proposition).
    let motive = Term::lam((**dom).clone(), (**body).clone());
    let rec_levels: Vec<Level> = if rec.num_levels == ind.num_levels + 1 {
        ls.iter().cloned().chain(std::iter::once(Level::Zero)).collect()
    } else {
        ls.clone()
    };

    // Peel the recursor type past the params and motive to reach the minor premises.
    let mut t = rec.ty.instantiate_levels(&rec_levels);
    for p in &params {
        let Term::Pi(_, _, b) = &t else { return None };
        t = b.instantiate(p);
    }
    let Term::Pi(_, _, b) = &t else { return None };
    t = b.instantiate(&motive);

    // Prove each constructor's minor premise.
    let mut minor_proofs = Vec::new();
    for _ in &ind.ctors {
        let Term::Pi(_, mdom, mbody) = &t else { return None };
        let mproof = prove_minor(k, mdom)?;
        t = mbody.instantiate(&mproof);
        minor_proofs.push(mproof);
    }

    // Assemble `I.rec.{…} params motive minor_proofs…` and have the kernel check it.
    let mut proof = Term::cnst(ind.recursor.clone(), rec_levels);
    for p in &params {
        proof = Term::app(proof, p.clone());
    }
    proof = Term::app(proof, motive);
    for mp in minor_proofs {
        proof = Term::app(proof, mp);
    }
    k.check(&proof, obligation).ok().map(|_| proof)
}

/// Prove one minor premise `Π fields/IHs. G[x := C fields]`: intro every binder (the
/// fields and their hypotheses), β-reduce the motive application to expose the real goal,
/// and close it with the leaf prover (which can use the IHs by assumption).
fn prove_minor(k: &Kernel, minor_ty: &Term) -> Option<Term> {
    let (doms, goal) = peel_all_pis(minor_ty.clone());
    // **Fully** normalize the goal (not just whnf): this contracts `(λx.G) (C fields)`
    // *and* reduces inside it (e.g. `add (succ k) 0 ↦ succ (add k 0)`), so the induction
    // hypothesis's left-hand side appears syntactically and the rewrite tactic can fire.
    let goal = crate::nbe::Nbe::new(k.env()).normalize_open(doms.len(), &goal);
    let leaf = prove_leaf(k, &doms, &goal)?;
    let mut p = leaf;
    for d in doms.into_iter().rev() {
        p = Term::lam(d, p);
    }
    Some(p)
}

/// Prove a goal under the context `doms` (the intro'd binders, outermost first), trying,
/// in order: **assumption** (a hypothesis whose type is definitionally the goal), `Eq`
/// by conversion (`Eq.refl`), `And` (`And.intro`, recursively), `Or` (try `Or.inl` then
/// `Or.inr`), and `True`. All structural, all kernel-checked — no unsound guessing.
fn prove_leaf(k: &Kernel, doms: &[Term], goal: &Term) -> Option<Term> {
    prove_leaf_fuel(k, doms, goal, 6)
}

/// As [`prove_leaf`], with a `fuel` budget bounding chained **rewrites** (using an `Eq`
/// hypothesis to rewrite the goal). The structural moves (assumption, refl, `And`/`Or`/
/// `True`) don't consume fuel; only a rewrite does, so the search always terminates.
fn prove_leaf_fuel(k: &Kernel, doms: &[Term], goal: &Term, fuel: u32) -> Option<Term> {
    let chk = Checker::new(k.env());
    let mut ctx = LocalCtx::new();
    for d in doms {
        ctx.push(d.clone());
    }

    // Assumption: is some hypothesis's type definitionally the goal?
    for i in 0..doms.len() {
        if let Some(ty) = ctx.var_type(i) {
            if chk.is_def_eq(&mut ctx, &ty, goal) {
                return Some(Term::Var(i));
            }
        }
    }

    let (head, args) = goal.unfold_apps();
    let structural = match &head {
        Term::Const(n, ls) if &**n == "Eq" && args.len() == 3 => {
            let (a, lhs, rhs) = (&args[0], &args[1], &args[2]);
            chk.is_def_eq(&mut ctx, lhs, rhs).then(|| {
                Term::apps(Term::cnst(name("Eq.refl"), ls.clone()), [a.clone(), lhs.clone()])
            })
        }
        // A conjunction: prove each side, combine with `And.intro`.
        Term::Const(n, _) if &**n == "And" && args.len() == 2 && k.env().contains("And.intro") => {
            (|| {
                let pa = prove_leaf_fuel(k, doms, &args[0], fuel)?;
                let pb = prove_leaf_fuel(k, doms, &args[1], fuel)?;
                Some(Term::apps(
                    Term::cnst(name("And.intro"), vec![]),
                    [args[0].clone(), args[1].clone(), pa, pb],
                ))
            })()
        }
        // A disjunction: prove the left (`Or.inl`) or, failing that, the right (`Or.inr`).
        Term::Const(n, _) if &**n == "Or" && args.len() == 2 && k.env().contains("Or.inl") => {
            if let Some(pa) = prove_leaf_fuel(k, doms, &args[0], fuel) {
                Some(Term::apps(
                    Term::cnst(name("Or.inl"), vec![]),
                    [args[0].clone(), args[1].clone(), pa],
                ))
            } else {
                prove_leaf_fuel(k, doms, &args[1], fuel).map(|pb| {
                    Term::apps(
                        Term::cnst(name("Or.inr"), vec![]),
                        [args[0].clone(), args[1].clone(), pb],
                    )
                })
            }
        }
        Term::Const(n, _) if &**n == "True" && k.env().contains("True.intro") => {
            Some(Term::cnst(name("True.intro"), vec![]))
        }
        _ => None,
    };
    if structural.is_some() {
        return structural;
    }
    // Rewrite: close an `Eq` goal by rewriting with an `Eq` hypothesis (congruence/IH).
    if fuel > 0 && matches!(&head, Term::Const(n, _) if &**n == "Eq") && args.len() == 3 {
        return try_rewrite(k, doms, goal, fuel);
    }
    None
}

/// Rewrite an `Eq` goal using some `Eq` hypothesis `h : a = b` in context: abstract `a`
/// out of the goal into a motive `M`, prove the rewritten goal `M b`, and transport back
/// with `Eq.subst`/`Eq.symm`. This is what lets an induction hypothesis close the step
/// case (e.g. `succ (add k 0) = succ k` from `add k 0 = k`).
fn try_rewrite(k: &Kernel, doms: &[Term], goal: &Term, fuel: u32) -> Option<Term> {
    if !k.env().contains("Eq.subst") || !k.env().contains("Eq.symm") {
        return None;
    }
    let chk = Checker::new(k.env());
    let r = Reducer::new(k.env());
    let mut ctx = LocalCtx::new();
    for d in doms {
        ctx.push(d.clone());
    }
    let nbe = crate::nbe::Nbe::new(k.env());
    let depth = doms.len();
    for i in 0..doms.len() {
        let Some(hty) = ctx.var_type(i) else { continue };
        let (hh, hargs) = r.whnf(&hty).unfold_apps();
        let Term::Const(hn, _) = &hh else { continue };
        if &**hn != "Eq" || hargs.len() != 3 {
            continue;
        }
        // Normalize the equation's sides to the **same** normal form as the (already
        // normalized) goal, so the left-hand side appears syntactically for the rewrite.
        let c = nbe.normalize_open(depth, &hargs[0]);
        let a = nbe.normalize_open(depth, &hargs[1]);
        let b = nbe.normalize_open(depth, &hargs[2]);
        if chk.is_def_eq(&mut ctx, &a, &b) {
            continue; // a trivial equality rewrites nothing
        }
        // Motive body `goal[a := z]` (under one binder `z`); skip if `a` doesn't occur.
        let mbody = crate::elab2::replace_with_var(&goal.lift(1, 0), &a.lift(1, 0), 0);
        if mbody == goal.lift(1, 0) {
            continue;
        }
        let motive = Term::lam(c.clone(), mbody.clone());
        let rewritten = mbody.instantiate(&b); // goal[a := b]  (β-applied motive)
        let Some(pb) = prove_leaf_fuel(k, doms, &rewritten, fuel - 1) else { continue };
        let Ok(u) = chk.infer_sort(&mut ctx, &c) else { continue };
        // Eq.subst C M b a (Eq.symm C a b h) pb : M a (= goal).
        let symm = Term::apps(
            Term::cnst(name("Eq.symm"), vec![u.clone()]),
            [c.clone(), a.clone(), b.clone(), Term::Var(i)],
        );
        let proof = Term::apps(
            Term::cnst(name("Eq.subst"), vec![u]),
            [c, motive, b, a, symm, pb],
        );
        return Some(proof);
    }
    None
}

/// If `body` is a `match` directly on one of the function's parameters, return
/// `(matched-parameter position, all parameter names, matched parameter name)`. This is
/// the shape a structurally-recursive function takes.
fn match_recursion(params: &[Binder], body: &Expr) -> Option<(usize, Vec<String>, String)> {
    let Expr::Match(scrut, _) = body.peel() else { return None };
    let Expr::Var(p, None) = scrut.peel() else { return None };
    let names: Vec<String> = params.iter().flat_map(|b| b.names.iter().cloned()).collect();
    let pos = names.iter().position(|n| n == p)?;
    Some((pos, names, p.clone()))
}

/// The declared type expression of parameter `name`, if present.
fn param_type<'a>(params: &'a [Binder], name: &str) -> Option<&'a Expr> {
    params.iter().find(|b| b.names.iter().any(|n| n == name)).map(|b| &b.ty)
}

/// Render a **normal-form** term as a readable value: a `Nat` succ/zero chain as a
/// decimal literal, any other constructor application as `C arg …` (parenthesising
/// nested applications), and a function/type as a placeholder.
/// A short human label for a command, used to prefix elaboration errors with the
/// definition being processed (so a failure in a multi-declaration `run` says *which*
/// `def`/`fn`/`prove` it was).
fn cmd_label(cmd: &Command) -> String {
    match cmd {
        Command::Fn { name, .. } => format!("fn '{name}'"),
        Command::Prove { name, .. } => format!("prove '{name}'"),
        Command::Def { name, .. } => format!("def '{name}'"),
        Command::Instance { name, .. } => format!("instance '{name}'"),
        Command::Check(_) => "check".to_string(),
        Command::Axiom { name, .. } => format!("axiom '{name}'"),
        Command::Inductive { name, .. } => format!("inductive '{name}'"),
        Command::Class(name) => format!("class '{name}'"),
        Command::Mutual(_) => "mutual block".to_string(),
    }
}

/// The head name of an application spine `f a b …` (the leftmost `Var`), if any. Used to
/// find the class an `instance`'s result type belongs to.
fn expr_head_name(e: &Expr) -> Option<String> {
    let mut cur = e.peel();
    loop {
        match cur {
            Expr::App(f, _) => cur = f.peel(),
            Expr::Var(n, _) => return Some(n.clone()),
            _ => return None,
        }
    }
}

pub fn render(env: &crate::Env, t: &Term) -> String {
    if let Some(n) = as_nat(t) {
        return n.to_string();
    }
    let (head, args) = t.unfold_apps();
    match &head {
        Term::Const(n, _) if args.is_empty() => n.to_string(),
        Term::Const(n, _) => {
            let rendered: Vec<String> = args.iter().map(|a| render_atom(env, a)).collect();
            format!("{n} {}", rendered.join(" "))
        }
        Term::Lam(..) | Term::Pi(..) => "<function>".to_string(),
        Term::Sort(_) => "<type>".to_string(),
        _ => format!("{t:?}"),
    }
}

/// Like [`render`] but parenthesises a non-atomic (applied) constructor.
fn render_atom(env: &crate::Env, t: &Term) -> String {
    let s = render(env, t);
    if as_nat(t).is_none() && matches!(t, Term::App(..)) {
        format!("({s})")
    } else {
        s
    }
}

/// If `t` is a `Nat` literal (`Nat.succ^n Nat.zero`), its value.
fn as_nat(t: &Term) -> Option<u64> {
    let mut n = 0u64;
    let mut cur = t.clone();
    loop {
        let (head, args) = cur.unfold_apps();
        match &head {
            Term::Const(nm, _) if &**nm == "Nat.zero" && args.is_empty() => return Some(n),
            Term::Const(nm, _) if &**nm == "Nat.succ" && args.len() == 1 => {
                n += 1;
                cur = args[0].clone();
            }
            _ => return None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generate::{eq_spec, nat_spec};
    use crate::level::Level;

    /// Declare `Nat`, `Eq`, `And`, and `add` (matching the kernel's proof builder).
    fn base() -> Session {
        let mut s = Session::new();
        s.k.declare_inductive(nat_spec()).unwrap();
        s.k.declare_inductive(eq_spec()).unwrap();
        s.run("inductive And (a : Prop) (b : Prop) : Prop | intro : a -> b -> And a b").unwrap();
        s.run(
            "def add (m : Nat) (n : Nat) : Nat := \
               Nat.rec.{1} (fun (_ : Nat) => Nat) n \
                 (fun (p : Nat) (ih : Nat) => Nat.succ ih) m",
        )
        .unwrap();
        // `Eq.symm`/`Eq.subst`, proven via `Eq.rec` — the rewrite tactic uses these.
        s.run(
            "def Eq.symm.{u} (A : Sort u) (a : A) (b : A) (h : Eq A a b) : Eq A b a := \
               Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => Eq A x a) (Eq.refl.{u} A a) b h",
        )
        .unwrap();
        s.run(
            "def Eq.subst.{u} (A : Sort u) (P : A -> Prop) (a : A) (b : A) (h : Eq A a b) (pa : P a) \
               : P b := Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => P x) pa b h",
        )
        .unwrap();
        s
    }

    /// The everyday case, in **Rust-like syntax**: calls are `f(args)`, specs are
    /// inline `ensures(..)` calls. Proven automatically at declaration.
    #[test]
    fn auto_proves_definitional_specs() {
        let mut s = base();
        // pick x ≡ x ; and add(0, x) ≡ x (add recurses on its first argument).
        s.run("fn pick(x: Nat) -> Nat { ensures(result == x); x }").unwrap();
        s.run("fn add_left_zero(x: Nat) -> Nat { ensures(result == x); add(Nat.zero, x) }")
            .unwrap();
        assert!(s.verified("pick"), "definitional spec should auto-prove");
        assert!(s.verified("add_left_zero"));
        assert!(s.all_verified());
    }

    /// **Implicit arguments**: a polymorphic identity whose type argument is implicit
    /// (`{A : Type}`). The caller writes `idt(n)` and the elaborator auto-inserts and
    /// solves the hole for `A`. The spec proves automatically (`idt n ≡ n`).
    #[test]
    fn implicit_type_argument_in_fn() {
        let mut s = base();
        s.run("def idt {A : Type} (x : A) : A := x").unwrap();
        s.run("fn use_idt(n: Nat) -> Nat { ensures(result == n); idt(n) }").unwrap();
        assert!(s.verified("use_idt"), "implicit A inferred and spec auto-proved");
    }

    /// The keystone, fully combined: a **universe-polymorphic implicit** — `id`'s type
    /// argument is implicit *and* its universe is polymorphic (`{A : Sort u}`). The
    /// caller writes just `idp(n)`; the elaborator auto-inserts `A`, solves `A := Nat`
    /// from the value, and propagates that to solve the level `u := 1`.
    #[test]
    fn polymorphic_implicit_infers_type_and_level() {
        let mut s = base();
        s.run("def idp.{u} {A : Sort u} (x : A) : A := x").unwrap();
        s.run("fn use_idp(n: Nat) -> Nat { ensures(result == n); idp(n) }").unwrap();
        assert!(s.verified("use_idp"), "both the implicit A and the level u are inferred");
    }

    /// **Universe-level inference**: `id` is universe-polymorphic, yet the call site
    /// omits the `.{u}` — the level is inferred from the explicit type argument `Nat`
    /// (whose own sort pins `u := 1`).
    #[test]
    fn universe_level_is_inferred() {
        let mut s = base();
        s.run("def id.{u} (A : Sort u) (x : A) : A := x").unwrap();
        // No `.{1}` here — inference fills it.
        s.run("fn use_id(n: Nat) -> Nat { ensures(result == n); id(Nat, n) }").unwrap();
        assert!(s.verified("use_id"), "level u inferred and spec auto-proved");
    }

    /// **Holes** (`_`) are solved by inference inside a `fn` body: the explicit type
    /// argument of `id` is written `_` and recovered from the value argument.
    #[test]
    fn hole_in_fn_body_is_solved() {
        let mut s = base();
        s.run("def id.{u} (A : Sort u) (x : A) : A := x").unwrap();
        s.run("fn use_hole(n: Nat) -> Nat { ensures(result == n); id(_, n) }").unwrap();
        assert!(s.verified("use_hole"), "the hole for A is solved to Nat");
    }

    /// **`match` as case analysis**: compiles to the inductive's recursor. `not(true)`
    /// computes to `false`, and the spec `not(Bool.true) == Bool.false` auto-proves.
    #[test]
    fn match_case_analysis() {
        let mut s = base();
        s.run("inductive Bool : Type | false : Bool | true : Bool").unwrap();
        s.run(
            "fn not(b: Bool) -> Bool { \
               match b { | Bool.true => Bool.false | Bool.false => Bool.true } }",
        )
        .unwrap();
        s.run("fn not_true(u: Bool) -> Bool { ensures(result == Bool.false); not(Bool.true) }")
            .unwrap();
        assert!(s.verified("not_true"), "not(true) ≡ false should auto-prove");
    }

    /// **Structural recursion via `match`**: the recursive-field induction hypothesis is
    /// bound as `<field>.rec`. `dbl` doubles a Nat; `dbl(2) ≡ 4` auto-proves.
    #[test]
    fn match_structural_recursion() {
        let mut s = base();
        // dbl 0 = 0 ; dbl (succ k) = succ (succ (dbl k))  — `k.rec` is `dbl k`.
        s.run(
            "fn dbl(n: Nat) -> Nat { \
               match n { \
                 | Nat.zero => Nat.zero \
                 | Nat.succ(k) => Nat.succ(Nat.succ(k.rec)) \
               } }",
        )
        .unwrap();
        // dbl 2 = 4
        s.run(
            "fn dbl_two(u: Nat) -> Nat { \
               ensures(result == Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))); \
               dbl(Nat.succ(Nat.succ(Nat.zero))) }",
        )
        .unwrap();
        assert!(s.verified("dbl_two"), "dbl 2 ≡ 4 should auto-prove by computation");
    }

    /// `match` over a **parameterised, recursive** inductive (`List`): `length` recurses
    /// through the `tail.rec` hypothesis. `length [0,0] ≡ 2`.
    #[test]
    fn match_recursion_on_list() {
        let mut s = base();
        s.run("inductive List (A : Type) : Type | nil : List A | cons : A -> List A -> List A")
            .unwrap();
        // `A` is an explicit parameter, so constructors take it positionally; the
        // pattern still binds only the two fields (head, tail), not the parameter.
        s.run(
            "fn length(xs: List Nat) -> Nat { \
               match xs { \
                 | List.nil => Nat.zero \
                 | List.cons(head, tail) => Nat.succ(tail.rec) \
               } }",
        )
        .unwrap();
        s.run(
            "fn len2(u: Nat) -> Nat { \
               ensures(result == Nat.succ(Nat.succ(Nat.zero))); \
               length(List.cons(Nat, Nat.zero, List.cons(Nat, Nat.zero, List.nil(Nat)))) }",
        )
        .unwrap();
        assert!(s.verified("len2"), "length [0,0] ≡ 2 should auto-prove");
    }

    /// **Dependent `match`** (proof by cases): the result type mentions the scrutinee, so
    /// the motive is dependent. `not(not(b)) == b` for all `b` — each branch proves the
    /// goal *specialised* to its constructor (`not(not(true)) ≡ true` etc.), closed by
    /// `Eq.refl` via computation.
    #[test]
    fn dependent_match_proof_by_cases() {
        let mut s = base();
        s.run("inductive Bool : Type | false : Bool | true : Bool").unwrap();
        s.run(
            "fn not(b: Bool) -> Bool { \
               match b { | Bool.true => Bool.false | Bool.false => Bool.true } }",
        )
        .unwrap();
        // ∀ b, not (not b) = b, by cases — the return type depends on `b`.
        s.run(
            "def not_not (b : Bool) : Eq.{1} Bool (not(not(b))) b := \
               match b { \
                 | Bool.true => Eq.refl.{1}(Bool, Bool.true) \
                 | Bool.false => Eq.refl.{1}(Bool, Bool.false) \
               }",
        )
        .expect("dependent match proof by cases should check");
        assert!(s.k.env().contains("not_not"));
    }

    /// **`match` on an indexed family** (`Vec A : Nat → Type`): the motive ranges over
    /// the index too. `vlen` recurses through `xs.rec`; `vlen [0] ≡ 1` auto-proves.
    #[test]
    fn match_on_indexed_family() {
        let mut s = base();
        s.run(
            "inductive Vec (A : Type) : Nat -> Type \
               | vnil : Vec A Nat.zero \
               | vcons : (n : Nat) -> A -> Vec A n -> Vec A (Nat.succ n)",
        )
        .unwrap();
        // length, ignoring the index — a constant-motive match on an indexed scrutinee.
        s.run(
            "fn vlen{k: Nat}(v: Vec Nat k) -> Nat { \
               match v { \
                 | Vec.vnil => Nat.zero \
                 | Vec.vcons(n, x, xs) => Nat.succ(xs.rec) \
               } }",
        )
        .unwrap();
        s.run(
            "fn vlen_one(u: Nat) -> Nat { \
               ensures(result == Nat.succ(Nat.zero)); \
               vlen(Vec.vcons(Nat, Nat.zero, Nat.zero, Vec.vnil(Nat))) }",
        )
        .unwrap();
        assert!(s.verified("vlen_one"), "length of a 1-element Vec ≡ 1 should auto-prove");
    }

    /// **Mutual inductives** end to end: `Tree`/`Forest` declared together via a
    /// `mutual { … }` block, then a *mutually-recursive* `tsize` written directly with
    /// the generated `Tree.rec` (which takes both motives and all three minors, and
    /// cross-invokes `Forest.rec` for the recursive `Forest` field). The cross-recursors
    /// **compute**: the size of a 3-node tree reduces to `3`, proven automatically.
    #[test]
    fn mutual_inductives_tree_forest() {
        let mut s = base();
        s.run(
            "mutual { \
               inductive Tree (A : Type) : Type \
                 | node : A -> Forest A -> Tree A \
               inductive Forest (A : Type) : Type \
                 | fnil : Forest A \
                 | fcons : Tree A -> Forest A -> Forest A \
             }",
        )
        .unwrap();
        assert!(s.k.env().contains("Tree.rec") && s.k.env().contains("Forest.rec"));
        // tsize t := Tree.rec.{1} Nat (λ_.Nat) (λ_.Nat)  -- both motives constant Nat
        //   (λ x f ih_f. succ ih_f)        -- node:  1 + size of its forest
        //   Nat.zero                       -- fnil:  0
        //   (λ t r ih_t ih_r. add ih_t ih_r)  -- fcons: sum of head + tail sizes
        //   t
        s.run(
            "def tsize (t : Tree Nat) : Nat := \
               Tree.rec.{1} Nat (fun (_ : Tree Nat) => Nat) (fun (_ : Forest Nat) => Nat) \
                 (fun (x : Nat) (f : Forest Nat) (ihf : Nat) => Nat.succ ihf) \
                 Nat.zero \
                 (fun (t2 : Tree Nat) (it : Nat) (r : Forest Nat) (ir : Nat) => add it ir) \
                 t",
        )
        .unwrap();
        // node(0, [node(0,nil), node(0,nil)]) — three nodes total.
        s.run(
            "fn three(u: Nat) -> Nat { \
               ensures(result == Nat.succ(Nat.succ(Nat.succ(Nat.zero)))); \
               tsize(Tree.node(Nat, Nat.zero, \
                 Forest.fcons(Nat, Tree.node(Nat, Nat.zero, Forest.fnil(Nat)), \
                   Forest.fcons(Nat, Tree.node(Nat, Nat.zero, Forest.fnil(Nat)), Forest.fnil(Nat))))) }",
        )
        .unwrap();
        assert!(s.verified("three"), "mutual-recursive tree size ≡ 3 should auto-prove");
    }

    /// **Execution**: a parameterless `fn main` is *evaluated* to a value (not just
    /// verified). `dbl 2` computes to `4`, rendered as the literal `"4"`.
    #[test]
    fn evaluate_entry_point() {
        let mut s = base();
        s.run("fn dbl(n: Nat) -> Nat { match n { | Nat.zero => Nat.zero | Nat.succ(k) => Nat.succ(Nat.succ(k.rec)) } }").unwrap();
        s.run("fn main(u: Nat) -> Nat { dbl(Nat.succ(Nat.succ(Nat.zero))) }").unwrap();
        // main takes a (dummy) arg here; evaluate the body directly via a 0-arg wrapper.
        s.run("def answer : Nat := dbl(Nat.succ(Nat.succ(Nat.zero)))").unwrap();
        assert_eq!(s.run_entry("answer").unwrap(), "4");
    }

    /// **Inferred self-recursion**: the recursive call is written by *name* (`dbl(k)`),
    /// not the `.rec` hypothesis — the compiler recognises it as structural recursion and
    /// compiles to the recursor. `dbl 2 ≡ 4`.
    #[test]
    fn name_recursion_single() {
        let mut s = base();
        s.run(
            "fn dbl(n: Nat) -> Nat { \
               match n { | Nat.zero => Nat.zero | Nat.succ(k) => Nat.succ(Nat.succ(dbl(k))) } }",
        )
        .unwrap();
        s.run("def two : Nat := dbl(Nat.succ(Nat.succ(Nat.zero)))").unwrap();
        assert_eq!(s.run_entry("two").unwrap(), "4");
    }

    /// **Inferred mutual recursion**: two ordinary `fn`s over a mutual inductive group,
    /// calling each other *by name* — no `mutual { }` block, no hand-written recursor. The
    /// compiler detects the bundle (by the inductive group) and compiles them jointly.
    /// `tsize` of a 3-node tree ≡ 3.
    #[test]
    fn name_recursion_mutual_bundle() {
        let mut s = base();
        s.run(
            "mutual { \
               inductive Tree (A : Type) : Type | node : A -> Forest A -> Tree A \
               inductive Forest (A : Type) : Type \
                 | fnil : Forest A | fcons : Tree A -> Forest A -> Forest A }",
        )
        .unwrap();
        // tsize and fsize call each other by name; auto-bundled.
        s.run(
            "fn tsize(t: Tree Nat) -> Nat { \
               match t { | Tree.node(x, f) => Nat.succ(fsize(f)) } } \
             fn fsize(xs: Forest Nat) -> Nat { \
               match xs { \
                 | Forest.fnil => Nat.zero \
                 | Forest.fcons(t, rest) => add(tsize(t), fsize(rest)) } }",
        )
        .unwrap();
        assert!(s.k.env().contains("tsize") && s.k.env().contains("fsize"));
        s.run(
            "def sz : Nat := \
               tsize(Tree.node(Nat, Nat.zero, \
                 Forest.fcons(Nat, Tree.node(Nat, Nat.zero, Forest.fnil(Nat)), \
                   Forest.fcons(Nat, Tree.node(Nat, Nat.zero, Forest.fnil(Nat)), Forest.fnil(Nat)))))",
        )
        .unwrap();
        assert_eq!(s.run_entry("sz").unwrap(), "3", "mutually-recursive tree size");
    }

    /// **Nested patterns**: `match` on a constructor whose sub-patterns are themselves
    /// constructors, with a fall-through catch-all. The pattern compiler desugars it into
    /// a tree of single-level matches.
    #[test]
    fn nested_pattern_match() {
        let mut s = base();
        s.run("inductive Bool : Type | false : Bool | true : Bool").unwrap();
        s.run("inductive Pair : Type | mk : Bool -> Bool -> Pair").unwrap();
        s.run(
            "fn both(p: Pair) -> Bool { \
               match p { \
                 | Pair.mk(Bool.true, Bool.true) => Bool.true \
                 | Pair.mk(a, b)                 => Bool.false } }",
        )
        .unwrap();
        s.run("def t1 : Bool := both(Pair.mk(Bool.true, Bool.true))").unwrap();
        s.run("def t2 : Bool := both(Pair.mk(Bool.true, Bool.false))").unwrap();
        assert_eq!(s.run_entry("t1").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("t2").unwrap(), "Bool.false");
    }

    /// **Wildcard / catch-all pattern**: a top-level variable arm covers all remaining
    /// constructors. `is_zero` checks for `Nat.zero` with a catch-all for the rest.
    #[test]
    fn wildcard_catch_all() {
        let mut s = base();
        s.run("inductive Bool : Type | false : Bool | true : Bool").unwrap();
        s.run(
            "fn is_zero(n: Nat) -> Bool { \
               match n { | Nat.zero => Bool.true | k => Bool.false } }",
        )
        .unwrap();
        s.run("def z : Bool := is_zero(Nat.zero)").unwrap();
        s.run("def nz : Bool := is_zero(Nat.succ(Nat.zero))").unwrap();
        assert_eq!(s.run_entry("z").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("nz").unwrap(), "Bool.false");
    }

    /// A non-exhaustive `match` (a missing constructor) is rejected, not silently
    /// accepted — there is no "default" hole in the recursor.
    #[test]
    fn match_non_exhaustive_is_rejected() {
        let mut s = base();
        s.run("inductive Bool : Type | false : Bool | true : Bool").unwrap();
        let r = s.run("fn bad(b: Bool) -> Bool { match b { | Bool.true => Bool.false } }");
        assert!(r.is_err(), "missing the Bool.false arm should be rejected");
    }

    /// `requires(..)` is an inline call too; it becomes a hypothesis in the obligation.
    #[test]
    fn auto_proves_with_precondition() {
        let mut s = base();
        s.run("fn g(x: Nat) -> Nat { requires(x == x); ensures(result == x); x }").unwrap();
        assert!(s.verified("g"));
    }

    /// **Assumption rule**: a postcondition that *is* a precondition is discharged by
    /// the hypothesis, not by conversion. `x = 0 ⊢ x = 0` is not a reflexivity (`x` is a
    /// variable) — the prover must use the hypothesis.
    #[test]
    fn auto_proves_by_assumption() {
        let mut s = base();
        s.run("fn h(x: Nat) -> Nat { requires(x == Nat.zero); ensures(x == Nat.zero); x }")
            .unwrap();
        assert!(s.verified("h"), "the postcondition is exactly the hypothesis");
    }

    /// **`Or` introduction**: a disjunctive postcondition is closed by proving one side
    /// (`Or.inl` here — the left is a reflexivity).
    #[test]
    fn auto_proves_disjunction() {
        let mut s = base();
        s.run("inductive Or (a : Prop) (b : Prop) : Prop | inl : a -> Or a b | inr : b -> Or a b")
            .unwrap();
        s.run(
            "fn orr(x: Nat) -> Nat { \
               ensures(Or(x == x, x == Nat.succ(x))); x }",
        )
        .unwrap();
        assert!(s.verified("orr"), "the left disjunct is provable, so Or.inl closes it");
    }

    /// **Induction tactic**: a universally-quantified theorem proved automatically by the
    /// recursor. `∀ (b : Bool), b = true ∨ b = false` — neither side is reflexivity for a
    /// variable `b`, so it needs case analysis; the prover applies `Bool.rec` and closes
    /// each case (`true = true`, `false = false`) by reflexivity.
    #[test]
    fn auto_proves_by_induction() {
        let mut s = base();
        s.run("inductive Bool : Type | false : Bool | true : Bool").unwrap();
        s.run("inductive Or (a : Prop) (b : Prop) : Prop | inl : a -> Or a b | inr : b -> Or a b")
            .unwrap();
        s.run(
            "fn bool_cases(b: Bool) -> Bool { \
               ensures(Or(b == Bool.true, b == Bool.false)); b }",
        )
        .unwrap();
        assert!(s.verified("bool_cases"), "the Bool dichotomy should auto-prove by induction");
    }

    /// Multiple `ensures(..)` calls are conjoined and each is proved.
    #[test]
    fn multiple_ensures() {
        let mut s = base();
        s.run("fn two(x: Nat) -> Nat { ensures(result == x); ensures(x == result); x }").unwrap();
        assert!(s.verified("two"));
    }

    /// **The induction + rewrite milestone**: `∀ x, x + 0 = x` — true only by induction
    /// (the step case needs the hypothesis `x + 0 = x` to rewrite `succ (x+0)` to
    /// `succ x`) — is now proved **automatically**. The prover applies `Nat.rec`, computes
    /// the base case, and closes the step case by rewriting with the IH.
    #[test]
    fn add_zero_auto_proves_by_induction_and_rewrite() {
        let mut s = base();
        s.run("fn add_zero(x: Nat) -> Nat { ensures(result == x); add(x, Nat.zero) }").unwrap();
        assert!(s.verified("add_zero"), "x + 0 = x should auto-prove by induction + rewrite");
    }

    /// A still-open obligation can be discharged by a supplied proof *term* — the
    /// injection point for an SMT/AI back-end. (`prove_with` checks it through the kernel.)
    #[test]
    fn manual_proof_term_discharges() {
        let mut s = base();
        // A goal the auto-prover leaves open (a bare axiom-style claim with no structure).
        s.run("axiom P : Prop").unwrap();
        s.run("axiom hp : P").unwrap();
        s.run("fn needs_p(u: Nat) -> Nat { ensures(P); u }").unwrap();
        assert!(!s.verified("needs_p"), "auto can't conjure a proof of an opaque P");
        // Discharge with the hypothesis term `λ u. hp`.
        let proof = Term::lam(
            Term::cnst(name("Nat"), vec![]),
            Term::cnst(name("hp"), vec![]),
        );
        s.prove_with("needs_p", proof).expect("supplied proof term discharges it");
        assert!(s.verified("needs_p"));
    }

    /// Soundness: a WRONG spec is never proven — auto-proof declines it, and a bogus
    /// hand certificate is rejected by the kernel.
    #[test]
    fn false_spec_cannot_be_proved() {
        let mut s = base();
        s.run("fn wrong(x: Nat) -> Nat { ensures(result == Nat.succ(x)); x }").unwrap();
        assert!(!s.verified("wrong"), "auto must not prove a false spec");
        let bogus = Term::lam(
            Term::cnst(name("Nat"), vec![]),
            Term::apps(
                Term::cnst(name("Eq.refl"), vec![Level::of_nat(1)]),
                [Term::cnst(name("Nat"), vec![]), Term::Var(0)],
            ),
        );
        assert!(s.prove_with("wrong", bogus).is_err());
        assert!(!s.verified("wrong"));
    }

    /// End to end: a whole Raven program in Rust-like syntax — `f(args)` calls, specs
    /// as inline `requires(..)`/`ensures(..)` calls — run in one shot, every
    /// definitional spec proven automatically.
    #[test]
    fn end_to_end_raven_program() {
        let mut s = base();
        let program = include_str!("raven/verify_program1.rv");
        s.run(program).expect("the program should run");
        assert!(s.all_verified(), "report:\n{}", s.report());
        assert_eq!(
            s.verified_fns(),
            vec![
                "const_zero".to_string(),
                "identity".to_string(),
                "left_unit".to_string(),
                "succ_of".to_string(),
            ]
        );
    }
}
