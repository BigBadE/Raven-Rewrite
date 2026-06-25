//! Stage D — compile the kernel's erased runtime terms to **bytecode** and run them on the
//! `rv-vm`, so the dependent fragment executes on the *same* engine as the executable
//! fragment (not the kernel's NbE reducer).
//!
//! The pipeline: a proof-fragment definition is type-checked by the kernel, erased to an
//! [`Erased`](rv_kernel::erase::Erased) term (untyped λ-calculus with constructor/def/recursor
//! constants — proofs already gone, by [crate erasure](rv_kernel::erase)), and lowered here
//! to [`rv_codegen::Bytecode`]. Two facts make this tractable:
//!
//! * **All control flow is in recursors.** The kernel compiles every `match`/recursion to a
//!   recursor, so a def body's erased term is straight-line λ-calculus — branching lives only
//!   inside the recursor functions we synthesize.
//! * **Recursors are structural.** A recursor switches on its scrutinee's constructor tag and
//!   calls the matching *minor* with the constructor's fields followed by the induction
//!   hypotheses (recursive results) — exactly the Lean convention the erased minors expect
//!   (e.g. `Nat.rec`'s successor minor is `λk λih. Succ ih`). So we synthesize each recursor
//!   from the constructors' recursive-field layout — no need for the stored `RecRule.rhs`.
//!
//! This crate is *outside* the trust base: a bug here can only produce a wrong value or fail
//! to compile, and the driver cross-checks the result against the kernel's own evaluation.

use rv_codegen::{Bytecode, CompiledFn, Const, Instr};
use rv_kernel::erase::{erase_def, Erased};
use rv_kernel::{Decl, Env, Term};
use rv_vm::Value;
use std::collections::HashMap;

/// Compile the runtime definition `entry` (and everything it transitively needs) to bytecode
/// and run it on the VM. Errors if it uses a construct this backend does not yet lower
/// (mutual or indexed recursors, higher-kinded type junk in a runtime position, …), so the
/// driver can fall back to the kernel's evaluation.
pub fn run_entry_on_vm(env: &Env, entry: &str) -> Result<Value, String> {
    let mut c = Compiler::new(env);
    c.ensure_def(entry)?;
    let bc = Bytecode { funcs: c.funcs };
    rv_vm::run(&bc, entry, &[])
}

struct Compiler<'a> {
    env: &'a Env,
    funcs: Vec<CompiledFn>,
    /// Stable index of each compiled function, keyed by its bytecode name.
    index: HashMap<String, usize>,
    /// Arity (parameter count) of each compiled function, known before its body is filled.
    arity: HashMap<String, usize>,
    /// Counter for synthesized lambda-lifted functions.
    lambda_ctr: usize,
}

impl<'a> Compiler<'a> {
    fn new(env: &'a Env) -> Self {
        Compiler { env, funcs: Vec::new(), index: HashMap::new(), arity: HashMap::new(), lambda_ctr: 0 }
    }

    /// Reserve a stable function slot under `name`, returning its index. The placeholder is
    /// overwritten once the body is compiled (so self/mutual references resolve).
    fn reserve(&mut self, name: &str, arity: usize) -> usize {
        if let Some(i) = self.index.get(name) {
            return *i;
        }
        let i = self.funcs.len();
        self.funcs.push(CompiledFn { name: name.to_string(), nparams: 0, nregs: 0, code: vec![], entry_off: 0 });
        self.index.insert(name.to_string(), i);
        self.arity.insert(name.to_string(), arity);
        i
    }

    // ---- top-level declarations ---------------------------------------------

    /// Ensure the def `name` is compiled; return its function index.
    fn ensure_def(&mut self, name: &str) -> Result<usize, String> {
        if let Some(i) = self.index.get(name) {
            return Ok(*i);
        }
        let body = erase_def(self.env, name)?;
        let (params, inner) = peel_lambdas(&body);
        let idx = self.reserve(name, params);
        let mut fb = FnBuilder::new(params);
        let mut scope: Vec<u32> = (0..params as u32).collect();
        let res = self.compile(&mut fb, &mut scope, inner)?;
        fb.code.push(Instr::Ret(res));
        self.funcs[idx] = fb.finish(name, params);
        Ok(idx)
    }

    /// Ensure the recursor `name` is compiled into a switching function; return its index.
    fn ensure_recursor(&mut self, name: &str) -> Result<usize, String> {
        if let Some(i) = self.index.get(name) {
            return Ok(*i);
        }
        let r = match self.env.get(name) {
            Some(Decl::Recursor(r)) => r.clone(),
            _ => return Err(format!("`{name}` is not a recursor")),
        };
        if r.num_indices != 0 {
            return Err(format!("recursor `{name}`: indexed elimination not yet lowered to bytecode"));
        }
        let ind = match self.env.get(&r.ind) {
            Some(Decl::Inductive(i)) => i.clone(),
            _ => return Err(format!("recursor `{name}`: missing inductive `{}`", r.ind)),
        };
        // Recursor parameter layout (params are erased): `motives… minors… major`. For a
        // single inductive `num_motives == 1`; for a mutual group it is the group size and
        // the minors run over *every* constructor of the group, ordered by group member then
        // per-type constructor index.
        let m = r.num_motives;
        let k = r.num_minors;
        let nparams = m + k + 1;
        let major_reg = (m + k) as u32;
        let motive_regs: Vec<u32> = (0..m as u32).collect();
        let minor_reg = |g: usize| (m + g) as u32; // g = global minor index
        let idx = self.reserve(name, nparams);

        // Global minor offset of the eliminated type within its mutual group: the number of
        // constructors in the members declared before it.
        let mut offset = 0usize;
        for member in &ind.group {
            if member == &r.ind {
                break;
            }
            offset += self.ctor_count(member)?;
        }

        let mut arms: Vec<(u32, usize)> = Vec::new(); // (per-type tag, arm offset)
        let mut code: Vec<Instr> = vec![Instr::Trap("recursor: no matching arm".into())]; // slot 0 = Switch, patched below
        let mut next_reg = nparams as u32;

        for ctor_name in &ind.ctors {
            let c = match self.env.get(ctor_name) {
                Some(Decl::Constructor(c)) => c.clone(),
                _ => return Err(format!("missing constructor `{ctor_name}`")),
            };
            // Per recursive field: which group member's recursor computes its IH (if any).
            let rec = recursive_fields(&c.ty, r.num_params, &ind.group);
            let arm_off = code.len();
            arms.push((c.index as u32, arm_off));

            // Build the minor's arguments exactly as the kernel's ι-rule does: for each field,
            // pass the field, and immediately after a *recursive* field pass its induction
            // hypothesis — `sibling_rec(motives…, minors…, field)`, dispatching to the recursor
            // of that field's (group-member) type.
            let mut args: Vec<u32> = Vec::new();
            for (f, member) in rec.iter().enumerate() {
                let fr = next_reg;
                next_reg += 1;
                code.push(Instr::Field(fr, major_reg, f as u32));
                args.push(fr);
                if let Some(member_ty) = member {
                    let sib_rec = self.recursor_name_of(member_ty)?;
                    let sib_idx = self.ensure_recursor(&sib_rec)?;
                    let ir = next_reg;
                    next_reg += 1;
                    let mut call_args: Vec<u32> = motive_regs.clone();
                    call_args.extend((0..k).map(minor_reg));
                    call_args.push(fr);
                    code.push(Instr::Call(ir, sib_idx, call_args));
                    args.push(ir);
                }
            }
            // The minor for this constructor is at its global index. A nullary case (no fields)
            // *is* the minor value itself; otherwise apply it one argument at a time (minors
            // are user lambdas — unary, curried).
            let g = offset + c.index;
            let res = if args.is_empty() {
                let r = next_reg;
                next_reg += 1;
                code.push(Instr::Move(r, minor_reg(g)));
                r
            } else {
                let mut f = minor_reg(g);
                for a in args {
                    let d = next_reg;
                    next_reg += 1;
                    code.push(Instr::CallClosure(d, f, vec![a]));
                    f = d;
                }
                f
            };
            code.push(Instr::Ret(res));
        }
        code[0] = Instr::Switch(major_reg, arms, None);
        self.funcs[idx] = CompiledFn {
            name: name.to_string(),
            nparams,
            nregs: next_reg as usize,
            code,
            entry_off: 0,
        };
        Ok(idx)
    }

    /// Ensure a constructor *wrapper* function (arity = field count, body = `MakeAdt`) exists,
    /// for when a constructor is used as a value or partially applied.
    fn ensure_ctor_wrapper(&mut self, ctor: &str, tag: u32, num_fields: usize) -> usize {
        let key = format!("ctor${ctor}");
        if let Some(i) = self.index.get(&key) {
            return *i;
        }
        let idx = self.reserve(&key, num_fields);
        let field_regs: Vec<u32> = (0..num_fields as u32).collect();
        let dst = num_fields as u32;
        let code = vec![Instr::MakeAdt(dst, tag, field_regs), Instr::Ret(dst)];
        self.funcs[idx] = CompiledFn { name: key, nparams: num_fields, nregs: num_fields + 1, code, entry_off: 0 };
        idx
    }

    // ---- expression compilation (straight-line; no branches) ----------------

    /// Compile `t` into `fb`, returning the register holding its value. `scope` maps de Bruijn
    /// indices to registers (innermost binder last).
    fn compile(&mut self, fb: &mut FnBuilder, scope: &mut Vec<u32>, t: &Erased) -> Result<u32, String> {
        match t {
            Erased::Var(i) => scope
                .get(scope.len().checked_sub(1 + *i).ok_or("erased: unbound variable")?)
                .copied()
                .ok_or_else(|| "erased: unbound variable".to_string()),
            Erased::Opaque => Ok(fb.emit_const(Const::Unit)),
            Erased::Const(name) => self.compile_const_value(fb, &name.to_string()),
            Erased::Lam(_) => self.lift_lambda(fb, scope, t),
            Erased::App(..) => {
                let (head, args) = unfold_app(t);
                // Compile arguments left-to-right.
                let mut arg_regs = Vec::with_capacity(args.len());
                for a in &args {
                    arg_regs.push(self.compile(fb, scope, a)?);
                }
                self.compile_apply(fb, scope, head, arg_regs)
            }
        }
    }

    /// Compile an application of `head` to already-evaluated `arg_regs`.
    fn compile_apply(
        &mut self,
        fb: &mut FnBuilder,
        scope: &mut Vec<u32>,
        head: &Erased,
        arg_regs: Vec<u32>,
    ) -> Result<u32, String> {
        match head {
            Erased::Const(name) => {
                let name = name.to_string();
                match self.env.get(&name) {
                    Some(Decl::Constructor(c)) => {
                        let (tag, nf) = (c.index as u32, c.num_fields);
                        if arg_regs.len() == nf {
                            Ok(fb.emit(|d| Instr::MakeAdt(d, tag, arg_regs.clone())))
                        } else if arg_regs.len() < nf {
                            let w = self.ensure_ctor_wrapper(&name, tag, nf);
                            Ok(fb.emit(|d| Instr::MakeClosure(d, w, arg_regs.clone())))
                        } else {
                            Err(format!("constructor `{name}` over-applied"))
                        }
                    }
                    Some(Decl::Def { .. }) => {
                        let idx = self.ensure_def(&name)?;
                        let ar = self.arity[&name];
                        Ok(self.emit_call(fb, idx, ar, arg_regs))
                    }
                    Some(Decl::Recursor(_)) => {
                        let idx = self.ensure_recursor(&name)?;
                        let ar = self.arity[&name];
                        Ok(self.emit_call(fb, idx, ar, arg_regs))
                    }
                    // A type former / sort applied in a runtime position is grade-0 junk that
                    // the result never inspects (e.g. a recursor's motive). Represent as Unit.
                    _ => Ok(fb.emit_const(Const::Unit)),
                }
            }
            Erased::Var(_) | Erased::Lam(_) | Erased::App(..) => {
                // A closure of statically-unknown arity: apply one argument at a time, since
                // lifted lambdas are unary (curried). Each `CallClosure` saturates exactly one
                // parameter and yields either the result or the next closure.
                let mut f = self.compile(fb, scope, head)?;
                for a in arg_regs {
                    f = fb.emit(|d| Instr::CallClosure(d, f, vec![a]));
                }
                Ok(f)
            }
            Erased::Opaque => Ok(fb.emit_const(Const::Unit)),
        }
    }

    /// A bare constant in value position.
    fn compile_const_value(&mut self, fb: &mut FnBuilder, name: &str) -> Result<u32, String> {
        match self.env.get(name) {
            Some(Decl::Constructor(c)) => {
                let (tag, nf) = (c.index as u32, c.num_fields);
                if nf == 0 {
                    Ok(fb.emit(|d| Instr::MakeAdt(d, tag, vec![])))
                } else {
                    let w = self.ensure_ctor_wrapper(name, tag, nf);
                    Ok(fb.emit(|d| Instr::MakeClosure(d, w, vec![])))
                }
            }
            Some(Decl::Def { .. }) => {
                let idx = self.ensure_def(name)?;
                let ar = self.arity[name];
                if ar == 0 {
                    Ok(fb.emit(|d| Instr::Call(d, idx, vec![])))
                } else {
                    Ok(fb.emit(|d| Instr::MakeClosure(d, idx, vec![])))
                }
            }
            Some(Decl::Recursor(_)) => {
                let idx = self.ensure_recursor(name)?;
                Ok(fb.emit(|d| Instr::MakeClosure(d, idx, vec![])))
            }
            // Inductive / Sort / unknown: type junk, never inspected at runtime.
            _ => Ok(fb.emit_const(Const::Unit)),
        }
    }

    /// Lambda-lift a single lambda `t = λ. body` to a fresh **unary** top-level function
    /// capturing its free variables, and emit a `MakeClosure` for it. A multi-argument lambda
    /// `λλ. …` lifts to nested unary closures (its body, itself a `Lam`, lifts again when
    /// compiled), so every closure has exactly one parameter — application is always one
    /// argument at a time, which avoids any arity mismatch on the fixed-arity VM.
    fn lift_lambda(&mut self, fb: &mut FnBuilder, scope: &mut Vec<u32>, t: &Erased) -> Result<u32, String> {
        let body = match t {
            Erased::Lam(b) => b.as_ref(),
            _ => return Err("lift_lambda: not a lambda".into()),
        };
        // Free variables of `λ. body`, as outer de Bruijn indices (relative to `scope`).
        let mut fvs: Vec<usize> = Vec::new();
        free_vars(body, 1, &mut fvs);
        fvs.sort_unstable();
        fvs.dedup();
        let m = fvs.len();
        let capture_regs: Vec<u32> = fvs.iter().map(|j| scope[scope.len() - 1 - j]).collect();

        // Lifted unary function: params are [captures…, the one lambda parameter].
        let name = format!("lambda${}", self.lambda_ctr);
        self.lambda_ctr += 1;
        let idx = self.reserve(&name, m + 1);

        // Build the lifted body's scope (innermost-last): de Bruijn 0 is the parameter (reg m);
        // de Bruijn j+1 is captured free variable j (reg = its position in `fvs`).
        let max_fv = fvs.last().map(|x| x + 1).unwrap_or(0);
        let len = 1 + max_fv;
        let mut inner_scope: Vec<u32> = vec![0; len];
        for k in 0..len {
            let d = len - 1 - k; // de Bruijn at this slot
            inner_scope[k] = if d == 0 {
                m as u32 // the lambda parameter
            } else if let Some(t) = fvs.iter().position(|&j| j == d - 1) {
                t as u32 // a captured free variable
            } else {
                0 // unreferenced filler (never read)
            };
        }
        let mut inner_fb = FnBuilder::new(m + 1);
        let res = self.compile(&mut inner_fb, &mut inner_scope, body)?;
        inner_fb.code.push(Instr::Ret(res));
        self.funcs[idx] = inner_fb.finish(&name, m + 1);

        Ok(fb.emit(|d| Instr::MakeClosure(d, idx, capture_regs.clone())))
    }

    /// Number of constructors of inductive `name`.
    fn ctor_count(&self, name: &rv_kernel::Name) -> Result<usize, String> {
        match self.env.get(name) {
            Some(Decl::Inductive(i)) => Ok(i.ctors.len()),
            _ => Err(format!("`{name}` is not an inductive")),
        }
    }

    /// The recursor name generated for inductive `name`.
    fn recursor_name_of(&self, name: &rv_kernel::Name) -> Result<String, String> {
        match self.env.get(name) {
            Some(Decl::Inductive(i)) => Ok(i.recursor.to_string()),
            _ => Err(format!("`{name}` is not an inductive")),
        }
    }

    /// Emit a call to function `idx` of arity `ar` with `args`, handling exact / partial /
    /// over-application.
    fn emit_call(&mut self, fb: &mut FnBuilder, idx: usize, ar: usize, args: Vec<u32>) -> u32 {
        use std::cmp::Ordering::*;
        match args.len().cmp(&ar) {
            Equal => fb.emit(|d| Instr::Call(d, idx, args.clone())),
            Less => fb.emit(|d| Instr::MakeClosure(d, idx, args.clone())),
            Greater => {
                // Saturate the function exactly, then apply the surplus one argument at a time
                // (the result is a closure of unknown arity).
                let (first, rest) = args.split_at(ar);
                let mut r = fb.emit(|d| Instr::Call(d, idx, first.to_vec()));
                for a in rest {
                    let a = *a;
                    r = fb.emit(|d| Instr::CallClosure(d, r, vec![a]));
                }
                r
            }
        }
    }
}

/// Per-function builder: a flat instruction stream plus a register bump-allocator.
struct FnBuilder {
    code: Vec<Instr>,
    next_reg: u32,
}
impl FnBuilder {
    fn new(nparams: usize) -> Self {
        FnBuilder { code: Vec::new(), next_reg: nparams as u32 }
    }
    fn fresh(&mut self) -> u32 {
        let r = self.next_reg;
        self.next_reg += 1;
        r
    }
    /// Emit an instruction whose only output is a fresh destination register; returns it.
    fn emit(&mut self, mk: impl FnOnce(u32) -> Instr) -> u32 {
        let d = self.fresh();
        self.code.push(mk(d));
        d
    }
    fn emit_const(&mut self, c: Const) -> u32 {
        let d = self.fresh();
        self.code.push(Instr::Const(d, c));
        d
    }
    fn finish(self, name: &str, nparams: usize) -> CompiledFn {
        CompiledFn { name: name.to_string(), nparams, nregs: self.next_reg as usize, code: self.code, entry_off: 0 }
    }
}

// ---- erased-term helpers ----------------------------------------------------

/// Peel leading lambdas: returns `(count, innermost body)`.
fn peel_lambdas(mut t: &Erased) -> (usize, &Erased) {
    let mut n = 0;
    while let Erased::Lam(b) = t {
        n += 1;
        t = b;
    }
    (n, t)
}

/// Flatten an application spine `head a0 a1 …` into `(head, [a0, a1, …])`.
fn unfold_app(t: &Erased) -> (&Erased, Vec<&Erased>) {
    let mut args = Vec::new();
    let mut cur = t;
    while let Erased::App(f, a) = cur {
        args.push(a.as_ref());
        cur = f;
    }
    args.reverse();
    (cur, args)
}

/// Collect the free de Bruijn indices of `t` (under `depth` local binders) as *outer*
/// indices `i - depth`.
fn free_vars(t: &Erased, depth: usize, out: &mut Vec<usize>) {
    match t {
        Erased::Var(i) => {
            if *i >= depth {
                out.push(*i - depth);
            }
        }
        Erased::Lam(b) => free_vars(b, depth + 1, out),
        Erased::App(f, a) => {
            free_vars(f, depth, out);
            free_vars(a, depth, out);
        }
        Erased::Const(_) | Erased::Opaque => {}
    }
}

/// For each of a constructor's fields, which mutual-group member it recursively refers to (its
/// type's head is a group member), or `None` for a non-recursive field. Walks the
/// constructor's `Π`-telescope, skips `num_params` parameters, and inspects each field's domain
/// head against the `group`.
fn recursive_fields(
    ctor_ty: &Term,
    num_params: usize,
    group: &[rv_kernel::Name],
) -> Vec<Option<rv_kernel::Name>> {
    let mut out = Vec::new();
    let mut ty = ctor_ty;
    let mut seen = 0usize;
    while let Term::Pi(_, dom, body) = ty {
        if seen >= num_params {
            let head = dom.unfold_apps().0;
            let member = match &head {
                Term::Const(n, _) => group.iter().find(|g| *g == n).cloned(),
                _ => None,
            };
            out.push(member);
        }
        seen += 1;
        ty = body;
    }
    out
}
