//! **A front end for the verified STLC** ([`crate::stlc`]) — a parser from human-readable
//! concrete syntax (with *named* variables) into the object language's `Exp` AST, with
//! **Hindley–Milner-style type inference** so λ-parameter annotations are optional.
//!
//! This is the "compile from text" piece: a program like
//!
//! ```text
//! let inc = \x. x + 1 in inc (inc 0)
//! ```
//!
//! is lexed, parsed into a named AST, **type-inferred** (each unannotated λ gets a fresh
//! unification variable, solved by unifying against use sites), and finally
//! **name-resolved to de Bruijn indices**, producing the surface term
//! `Exp.elet(Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(0), Exp.enat(1))), …)` that the kernel
//! elaborates, the verified checker (`ok`/`synth`) type-checks, and the evaluator (`run`)
//! executes. The parser/inferencer is ordinary (untrusted) Rust — it only produces a term;
//! soundness still rests entirely on the kernel checking what it emits. An inferred
//! annotation that is wrong simply yields a term the verified checker rejects.
//!
//! Grammar (precedence low→high): `let`/`if`/`\`-abstraction, then `+`, then application,
//! then atoms. λ params may be annotated (`\x:nat. e`) or bare (`\x. e`). Types are `nat`,
//! `bool`, and right-associative arrows `T -> T`.

/// Parse an STLC program (concrete syntax) into the `Exp` surface term, resolving names to
/// de Bruijn indices and inferring any omitted λ annotations. Returns the term as a string
/// ready to splice into a `def … : Exp := …`.
pub fn parse(src: &str) -> Result<String, String> {
    let toks = lex(src)?;
    let mut p = Parser { src, toks, pos: 0 };
    let ast = p.expr()?;
    if p.pos != p.toks.len() {
        return Err(p.err_here("unexpected trailing input"));
    }
    // Infer/solve all λ-parameter types, then emit the fully-annotated de Bruijn term.
    let mut inf = Infer::new();
    let mut env: Vec<(String, Ty)> = Vec::new();
    inf.infer(&ast, &mut env)?;
    let mut scope: Vec<String> = Vec::new();
    emit(&ast, &inf, &mut scope)
}

/// Render a diagnostic anchored at byte offset `off` in `src`: `line:col: msg`, followed by
/// the offending source line and a caret under the column. Offsets at or past the end point
/// at end-of-input. ASCII-oriented (the STLC surface syntax is ASCII), counting bytes as
/// columns; a non-ASCII byte just yields a slightly-off caret, never a panic.
fn pos_err(src: &str, off: usize, msg: &str) -> String {
    let off = off.min(src.len());
    let line_start = src[..off].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_end = src[off..].find('\n').map(|i| off + i).unwrap_or(src.len());
    let line_no = src[..off].bytes().filter(|&b| b == b'\n').count() + 1;
    let col = off - line_start; // 0-based column within the line
    let line = &src[line_start..line_end];
    let caret = format!("{}^", " ".repeat(col));
    format!("{line_no}:{}: {msg}\n  {line}\n  {caret}", col + 1)
}

// ---------------------------------------------------------------------------- lexer

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Num(u64),
    Lam,
    Dot,
    Colon,
    Eq,
    Plus,
    Star,
    Comma,
    Arrow,
    LParen,
    RParen,
    Let,
    Rec,
    In,
    If,
    Then,
    Else,
    True,
    False,
    Nat,
    Bool,
    Fst,
    Snd,
}

/// Lex into tokens each paired with the **byte offset** where it begins, so parser errors
/// can point at the exact source location.
fn lex(src: &str) -> Result<Vec<(Tok, usize)>, String> {
    let b = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() {
        let c = b[i];
        let start = i;
        let tok = if c.is_ascii_whitespace() {
            i += 1;
            continue;
        } else if c == b'-' && i + 1 < b.len() && b[i + 1] == b'>' {
            i += 2;
            Tok::Arrow
        } else if c == b'\\' {
            i += 1;
            Tok::Lam
        } else if c == b'.' {
            i += 1;
            Tok::Dot
        } else if c == b':' {
            i += 1;
            Tok::Colon
        } else if c == b'=' {
            i += 1;
            Tok::Eq
        } else if c == b'+' {
            i += 1;
            Tok::Plus
        } else if c == b'*' {
            i += 1;
            Tok::Star
        } else if c == b',' {
            i += 1;
            Tok::Comma
        } else if c == b'(' {
            i += 1;
            Tok::LParen
        } else if c == b')' {
            i += 1;
            Tok::RParen
        } else if c.is_ascii_digit() {
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            let n: u64 = src[start..i]
                .parse()
                .map_err(|_| pos_err(src, start, "number literal out of range"))?;
            Tok::Num(n)
        } else if c.is_ascii_alphabetic() || c == b'_' {
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            match &src[start..i] {
                "let" => Tok::Let,
                "rec" => Tok::Rec,
                "in" => Tok::In,
                "if" => Tok::If,
                "then" => Tok::Then,
                "else" => Tok::Else,
                "true" => Tok::True,
                "false" => Tok::False,
                "nat" => Tok::Nat,
                "bool" => Tok::Bool,
                "fst" => Tok::Fst,
                "snd" => Tok::Snd,
                w => Tok::Ident(w.to_string()),
            }
        } else {
            return Err(pos_err(src, start, &format!("unexpected character '{}'", c as char)));
        };
        out.push((tok, start));
    }
    Ok(out)
}

// ----------------------------------------------------------------------------- AST

/// A named-variable AST. Distinct from the de Bruijn `Exp` the kernel sees: names are
/// resolved (and λ types inferred) only after the whole tree — and so all use sites — is known.
#[derive(Clone, Debug)]
enum Ast {
    Var(String),
    Nat(u64),
    Bool(bool),
    Add(Box<Ast>, Box<Ast>),
    /// `let name = bound in body`.
    Let(String, Box<Ast>, Box<Ast>),
    /// `let rec name[:ann] = body in rest` — `name` is recursively bound in `body`. Desugars
    /// to `let name = (fix name. body) in rest`, i.e. `Exp.elet(Exp.efix(T, body), rest)`.
    LetRec { name: String, ann: Option<Ty>, body: Box<Ast>, rest: Box<Ast> },
    /// `\name[:ann]. body`. `ann` is the optional source annotation. The (possibly inferred)
    /// parameter type lives in the solver, keyed by source pre-order via `Infer::lam_tv`.
    Lam { name: String, ann: Option<Ty>, body: Box<Ast> },
    App(Box<Ast>, Box<Ast>),
    If(Box<Ast>, Box<Ast>, Box<Ast>),
    Pair(Box<Ast>, Box<Ast>),
    Fst(Box<Ast>),
    Snd(Box<Ast>),
}

/// An inference type. `Var` is a unification variable (index into the solver's store).
#[derive(Clone, Debug, PartialEq)]
enum Ty {
    Nat,
    Bool,
    Arrow(Box<Ty>, Box<Ty>),
    Prod(Box<Ty>, Box<Ty>),
    Var(usize),
}

// --------------------------------------------------------------------------- parser

struct Parser<'a> {
    src: &'a str,
    toks: Vec<(Tok, usize)>,
    pos: usize,
}

impl Parser<'_> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|(t, _)| t)
    }
    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).map(|(t, _)| t.clone());
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    /// The byte offset of the current token, or end-of-input.
    fn cur_offset(&self) -> usize {
        self.toks.get(self.pos).map(|(_, o)| *o).unwrap_or(self.src.len())
    }
    /// A positioned diagnostic anchored at the current token.
    fn err_here(&self, msg: &str) -> String {
        pos_err(self.src, self.cur_offset(), msg)
    }
    fn eat(&mut self, t: &Tok) -> Result<(), String> {
        if self.peek() == Some(t) {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.err_here(&format!("expected {}, found {}", describe(t), self.found())))
        }
    }
    /// A human-readable description of the current (or end-of-input) token, for messages.
    fn found(&self) -> String {
        match self.peek() {
            Some(t) => describe(t),
            None => "end of input".to_string(),
        }
    }

    /// expr := lambda | let | if | additive
    fn expr(&mut self) -> Result<Ast, String> {
        match self.peek() {
            Some(Tok::Lam) => self.lambda(),
            Some(Tok::Let) => self.let_(),
            Some(Tok::If) => self.if_(),
            _ => self.additive(),
        }
    }

    fn lambda(&mut self) -> Result<Ast, String> {
        self.eat(&Tok::Lam)?;
        let name = self.ident()?;
        // Annotation is now optional: `\x. e` or `\x:T. e`.
        let ann = if self.peek() == Some(&Tok::Colon) {
            self.pos += 1;
            Some(self.ty()?)
        } else {
            None
        };
        self.eat(&Tok::Dot)?;
        let body = self.expr()?;
        Ok(Ast::Lam { name, ann, body: Box::new(body) })
    }

    fn let_(&mut self) -> Result<Ast, String> {
        self.eat(&Tok::Let)?;
        if self.peek() == Some(&Tok::Rec) {
            return self.let_rec();
        }
        let name = self.ident()?;
        self.eat(&Tok::Eq)?;
        let bound = self.expr()?; // bound expr is in the *outer* scope
        self.eat(&Tok::In)?;
        let body = self.expr()?;
        Ok(Ast::Let(name, Box::new(bound), Box::new(body)))
    }

    /// `let rec name[:ann] = body in rest`.
    fn let_rec(&mut self) -> Result<Ast, String> {
        self.eat(&Tok::Rec)?;
        let name = self.ident()?;
        let ann = if self.peek() == Some(&Tok::Colon) {
            self.pos += 1;
            Some(self.ty()?)
        } else {
            None
        };
        self.eat(&Tok::Eq)?;
        let body = self.expr()?; // `name` is recursively in scope inside `body`
        self.eat(&Tok::In)?;
        let rest = self.expr()?;
        Ok(Ast::LetRec { name, ann, body: Box::new(body), rest: Box::new(rest) })
    }

    fn if_(&mut self) -> Result<Ast, String> {
        self.eat(&Tok::If)?;
        let c = self.expr()?;
        self.eat(&Tok::Then)?;
        let t = self.expr()?;
        self.eat(&Tok::Else)?;
        let e = self.expr()?;
        Ok(Ast::If(Box::new(c), Box::new(t), Box::new(e)))
    }

    /// additive := application ('+' application)*  (left-associative)
    fn additive(&mut self) -> Result<Ast, String> {
        let mut lhs = self.application()?;
        while self.peek() == Some(&Tok::Plus) {
            self.pos += 1;
            let rhs = self.application()?;
            lhs = Ast::Add(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    /// application := atom atom*  (left-associative)
    fn application(&mut self) -> Result<Ast, String> {
        let mut f = self.atom()?;
        while self.starts_atom() {
            let a = self.atom()?;
            f = Ast::App(Box::new(f), Box::new(a));
        }
        Ok(f)
    }

    fn starts_atom(&self) -> bool {
        matches!(
            self.peek(),
            Some(
                Tok::Num(_) | Tok::True | Tok::False | Tok::Ident(_) | Tok::LParen
                    | Tok::Fst | Tok::Snd
            )
        )
    }

    fn atom(&mut self) -> Result<Ast, String> {
        // Anchor any error at this token before consuming it.
        let err = self.err_here(&format!("expected an expression, found {}", self.found()));
        match self.bump() {
            Some(Tok::Num(n)) => Ok(Ast::Nat(n)),
            Some(Tok::True) => Ok(Ast::Bool(true)),
            Some(Tok::False) => Ok(Ast::Bool(false)),
            Some(Tok::Ident(name)) => Ok(Ast::Var(name)),
            Some(Tok::Fst) => Ok(Ast::Fst(Box::new(self.atom()?))),
            Some(Tok::Snd) => Ok(Ast::Snd(Box::new(self.atom()?))),
            Some(Tok::LParen) => {
                let e = self.expr()?;
                // `(a, b)` is a pair; `(e)` is just grouping.
                if self.peek() == Some(&Tok::Comma) {
                    self.pos += 1;
                    let e2 = self.expr()?;
                    self.eat(&Tok::RParen)?;
                    Ok(Ast::Pair(Box::new(e), Box::new(e2)))
                } else {
                    self.eat(&Tok::RParen)?;
                    Ok(e)
                }
            }
            _ => Err(err),
        }
    }

    fn ident(&mut self) -> Result<String, String> {
        let err = self.err_here(&format!("expected an identifier, found {}", self.found()));
        match self.bump() {
            Some(Tok::Ident(s)) => Ok(s),
            _ => Err(err),
        }
    }

    /// ty := prodTy ('->' ty)?   (arrow right-associative, binds looser than `*`)
    fn ty(&mut self) -> Result<Ty, String> {
        let dom = self.ty_prod()?;
        if self.peek() == Some(&Tok::Arrow) {
            self.pos += 1;
            let cod = self.ty()?;
            Ok(Ty::Arrow(Box::new(dom), Box::new(cod)))
        } else {
            Ok(dom)
        }
    }

    /// prodTy := tyatom ('*' tyatom)*   (left-associative)
    fn ty_prod(&mut self) -> Result<Ty, String> {
        let mut t = self.ty_atom()?;
        while self.peek() == Some(&Tok::Star) {
            self.pos += 1;
            let r = self.ty_atom()?;
            t = Ty::Prod(Box::new(t), Box::new(r));
        }
        Ok(t)
    }

    fn ty_atom(&mut self) -> Result<Ty, String> {
        let err = self.err_here(&format!("expected a type, found {}", self.found()));
        match self.bump() {
            Some(Tok::Nat) => Ok(Ty::Nat),
            Some(Tok::Bool) => Ok(Ty::Bool),
            Some(Tok::LParen) => {
                let t = self.ty()?;
                self.eat(&Tok::RParen)?;
                Ok(t)
            }
            _ => Err(err),
        }
    }
}

/// A short, human-readable description of a token for diagnostics.
fn describe(t: &Tok) -> String {
    match t {
        Tok::Ident(s) => format!("identifier `{s}`"),
        Tok::Num(n) => format!("number `{n}`"),
        Tok::Lam => "`\\`".to_string(),
        Tok::Dot => "`.`".to_string(),
        Tok::Colon => "`:`".to_string(),
        Tok::Eq => "`=`".to_string(),
        Tok::Plus => "`+`".to_string(),
        Tok::Star => "`*`".to_string(),
        Tok::Comma => "`,`".to_string(),
        Tok::Arrow => "`->`".to_string(),
        Tok::LParen => "`(`".to_string(),
        Tok::RParen => "`)`".to_string(),
        Tok::Let => "`let`".to_string(),
        Tok::Rec => "`rec`".to_string(),
        Tok::In => "`in`".to_string(),
        Tok::If => "`if`".to_string(),
        Tok::Then => "`then`".to_string(),
        Tok::Else => "`else`".to_string(),
        Tok::True => "`true`".to_string(),
        Tok::False => "`false`".to_string(),
        Tok::Nat => "`nat`".to_string(),
        Tok::Bool => "`bool`".to_string(),
        Tok::Fst => "`fst`".to_string(),
        Tok::Snd => "`snd`".to_string(),
    }
}

// ------------------------------------------------------------------------ inference

/// A first-order unification engine over `Ty`. Union-find-free: a flat substitution store
/// where `subst[i]` is `Some(t)` once variable `i` is solved.
struct Infer {
    subst: Vec<Option<Ty>>,
    /// The unification variable carrying each λ's parameter type, in source pre-order. Filled
    /// by `infer`, read positionally by `emit` (which re-traverses in the same order).
    lam_tv: Vec<usize>,
    /// Likewise the variable carrying each `let rec`'s declared type (the fixpoint's type).
    fix_tv: Vec<usize>,
}

impl Infer {
    fn new() -> Self {
        Infer { subst: Vec::new(), lam_tv: Vec::new(), fix_tv: Vec::new() }
    }

    fn fresh(&mut self) -> usize {
        self.subst.push(None);
        self.subst.len() - 1
    }

    /// Follow the substitution to a representative (shallow — one level of `Var`).
    fn resolve(&self, t: &Ty) -> Ty {
        match t {
            Ty::Var(i) => match &self.subst[*i] {
                Some(u) => self.resolve(u),
                None => Ty::Var(*i),
            },
            _ => t.clone(),
        }
    }

    /// Does variable `v` occur in `t` (after resolution)? Prevents infinite types.
    fn occurs(&self, v: usize, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Var(i) => i == v,
            Ty::Arrow(a, b) => self.occurs(v, &a) || self.occurs(v, &b),
            Ty::Prod(a, b) => self.occurs(v, &a) || self.occurs(v, &b),
            _ => false,
        }
    }

    fn unify(&mut self, a: &Ty, b: &Ty) -> Result<(), String> {
        let a = self.resolve(a);
        let b = self.resolve(b);
        match (a, b) {
            (Ty::Nat, Ty::Nat) | (Ty::Bool, Ty::Bool) => Ok(()),
            (Ty::Arrow(a1, a2), Ty::Arrow(b1, b2)) => {
                self.unify(&a1, &b1)?;
                self.unify(&a2, &b2)
            }
            (Ty::Prod(a1, a2), Ty::Prod(b1, b2)) => {
                self.unify(&a1, &b1)?;
                self.unify(&a2, &b2)
            }
            (Ty::Var(i), Ty::Var(j)) if i == j => Ok(()),
            (Ty::Var(i), other) | (other, Ty::Var(i)) => {
                if self.occurs(i, &other) {
                    return Err("occurs-check failure (infinite type)".to_string());
                }
                self.subst[i] = Some(other);
                Ok(())
            }
            (x, y) => Err(format!("cannot unify {x:?} with {y:?}")),
        }
    }

    /// Infer the type of `ast` under the name→type environment `env` (innermost last).
    /// Mutates λ nodes' `tv` slots via the `lam_tv` side table so `emit` can read them.
    fn infer(&mut self, ast: &Ast, env: &mut Vec<(String, Ty)>) -> Result<Ty, String> {
        match ast {
            Ast::Var(name) => env
                .iter()
                .rev()
                .find(|(n, _)| n == name)
                .map(|(_, t)| t.clone())
                .ok_or_else(|| format!("unbound variable '{name}'")),
            Ast::Nat(_) => Ok(Ty::Nat),
            Ast::Bool(_) => Ok(Ty::Bool),
            Ast::Add(a, b) => {
                let ta = self.infer(a, env)?;
                self.unify(&ta, &Ty::Nat)?;
                let tb = self.infer(b, env)?;
                self.unify(&tb, &Ty::Nat)?;
                Ok(Ty::Nat)
            }
            Ast::Let(name, bound, body) => {
                let tb = self.infer(bound, env)?;
                env.push((name.clone(), tb));
                let r = self.infer(body, env);
                env.pop();
                r
            }
            Ast::LetRec { name, ann, body, rest } => {
                // The fixpoint's type: its annotation, else a fresh var the body constrains.
                let fty = match ann {
                    Some(t) => t.clone(),
                    None => Ty::Var(self.fresh()),
                };
                let v = self.var_of(&fty);
                self.fix_tv.push(v);
                // `name` is in scope (at its own type) inside its own body; the body must
                // have that very type (it IS the fixpoint's unfolding).
                env.push((name.clone(), fty.clone()));
                let bty = self.infer(body, env)?;
                env.pop();
                self.unify(&bty, &fty)?;
                // ...and `name` is bound (at `fty`) in the rest.
                env.push((name.clone(), fty.clone()));
                let r = self.infer(rest, env);
                env.pop();
                r
            }
            Ast::Lam { name, ann, body } => {
                // Parameter type: the annotation if present, else a fresh unification var.
                let pty = match ann {
                    Some(t) => t.clone(),
                    None => Ty::Var(self.fresh()),
                };
                // Record which variable carries this λ's parameter type, in source pre-order
                // (the order `emit` re-traverses), so emission can read it back by position.
                let v = self.var_of(&pty);
                self.lam_tv.push(v);
                env.push((name.clone(), pty.clone()));
                let bty = self.infer(body, env);
                env.pop();
                Ok(Ty::Arrow(Box::new(pty), Box::new(bty?)))
            }
            Ast::App(f, a) => {
                let tf = self.infer(f, env)?;
                let ta = self.infer(a, env)?;
                let tr = Ty::Var(self.fresh());
                let want = Ty::Arrow(Box::new(ta), Box::new(tr.clone()));
                self.unify(&tf, &want)?;
                Ok(tr)
            }
            Ast::If(c, t, e) => {
                let tc = self.infer(c, env)?;
                self.unify(&tc, &Ty::Bool)?;
                let tt = self.infer(t, env)?;
                let te = self.infer(e, env)?;
                self.unify(&tt, &te)?;
                Ok(tt)
            }
            Ast::Pair(a, b) => {
                let ta = self.infer(a, env)?;
                let tb = self.infer(b, env)?;
                Ok(Ty::Prod(Box::new(ta), Box::new(tb)))
            }
            Ast::Fst(e) => {
                let te = self.infer(e, env)?;
                let x = Ty::Var(self.fresh());
                let y = Ty::Var(self.fresh());
                self.unify(&te, &Ty::Prod(Box::new(x.clone()), Box::new(y)))?;
                Ok(x)
            }
            Ast::Snd(e) => {
                let te = self.infer(e, env)?;
                let x = Ty::Var(self.fresh());
                let y = Ty::Var(self.fresh());
                self.unify(&te, &Ty::Prod(Box::new(x), Box::new(y.clone())))?;
                Ok(y)
            }
        }
    }

    /// The unification variable underlying a parameter type, allocating one for a concrete
    /// annotation so every λ has a uniform `Var` slot to resolve at emit time.
    fn var_of(&mut self, t: &Ty) -> usize {
        match t {
            Ty::Var(i) => *i,
            other => {
                let v = self.fresh();
                self.subst[v] = Some(other.clone());
                v
            }
        }
    }

    /// Fully resolve `t` to a ground `Ty` (no remaining variables), or error if ambiguous.
    fn ground(&self, t: &Ty) -> Result<Ty, String> {
        match self.resolve(t) {
            Ty::Nat => Ok(Ty::Nat),
            Ty::Bool => Ok(Ty::Bool),
            Ty::Arrow(a, b) => Ok(Ty::Arrow(Box::new(self.ground(&a)?), Box::new(self.ground(&b)?))),
            Ty::Prod(a, b) => Ok(Ty::Prod(Box::new(self.ground(&a)?), Box::new(self.ground(&b)?))),
            Ty::Var(_) => Err(
                "ambiguous type: a λ-parameter type could not be inferred (add an annotation)"
                    .to_string(),
            ),
        }
    }
}

// -------------------------------------------------------------------------- emitter

/// Pre-order cursors into the solver's λ / `let rec` side-tables, advanced as `emit`
/// re-traverses the AST in the same order `infer` filled them.
#[derive(Default)]
struct Cursors {
    lam: usize,
    fix: usize,
}

/// Emit the fully-annotated de Bruijn `Exp` term, reading λ / fix types from the solver.
/// Visits binders in the same pre-order as `Infer::infer`, so the side-table slots line up.
fn emit(ast: &Ast, inf: &Infer, scope: &mut Vec<String>) -> Result<String, String> {
    let mut cur = Cursors::default();
    emit_go(ast, inf, scope, &mut cur)
}

fn emit_go(
    ast: &Ast,
    inf: &Infer,
    scope: &mut Vec<String>,
    cur: &mut Cursors,
) -> Result<String, String> {
    match ast {
        Ast::Var(name) => {
            let idx = resolve(scope, name)?;
            Ok(format!("Exp.evar({})", nat_lit(idx as u64)))
        }
        Ast::Nat(n) => Ok(format!("Exp.enat({})", nat_lit(*n))),
        Ast::Bool(true) => Ok("Exp.ebool(Bool.true)".to_string()),
        Ast::Bool(false) => Ok("Exp.ebool(Bool.false)".to_string()),
        Ast::Add(a, b) => {
            let ea = emit_go(a, inf, scope, cur)?;
            let eb = emit_go(b, inf, scope, cur)?;
            Ok(format!("Exp.eadd({}, {})", ea, eb))
        }
        Ast::Let(name, bound, body) => {
            let eb = emit_go(bound, inf, scope, cur)?;
            scope.push(name.clone());
            let ebody = emit_go(body, inf, scope, cur);
            scope.pop();
            Ok(format!("Exp.elet({}, {})", eb, ebody?))
        }
        Ast::LetRec { name, body, rest, .. } => {
            // `let rec f = body in rest` ≡ `let f = (fix f. body) in rest`. Both `body` and
            // `rest` see `f` at de Bruijn 0 (the fix's self-binder, and the let's binding).
            let slot = cur.fix;
            cur.fix += 1;
            let tv = inf.fix_tv[slot];
            let ty = inf.ground(&Ty::Var(tv))?;
            scope.push(name.clone());
            let ebody = emit_go(body, inf, scope, cur);
            scope.pop();
            let ebody = ebody?;
            scope.push(name.clone());
            let erest = emit_go(rest, inf, scope, cur);
            scope.pop();
            Ok(format!("Exp.elet(Exp.efix({}, {}), {})", emit_ty(&ty), ebody, erest?))
        }
        Ast::Lam { name, body, .. } => {
            // This λ's parameter-type variable is the next slot in source pre-order.
            let slot = cur.lam;
            cur.lam += 1;
            let tv = inf.lam_tv[slot];
            let ty = inf.ground(&Ty::Var(tv))?;
            scope.push(name.clone());
            let ebody = emit_go(body, inf, scope, cur);
            scope.pop();
            Ok(format!("Exp.elam({}, {})", emit_ty(&ty), ebody?))
        }
        Ast::App(f, a) => {
            let ef = emit_go(f, inf, scope, cur)?;
            let ea = emit_go(a, inf, scope, cur)?;
            Ok(format!("Exp.eapp({}, {})", ef, ea))
        }
        Ast::If(c, t, e) => {
            let ec = emit_go(c, inf, scope, cur)?;
            let et = emit_go(t, inf, scope, cur)?;
            let ee = emit_go(e, inf, scope, cur)?;
            Ok(format!("Exp.eif({}, {}, {})", ec, et, ee))
        }
        Ast::Pair(a, b) => {
            let ea = emit_go(a, inf, scope, cur)?;
            let eb = emit_go(b, inf, scope, cur)?;
            Ok(format!("Exp.epair({}, {})", ea, eb))
        }
        Ast::Fst(e) => Ok(format!("Exp.efst({})", emit_go(e, inf, scope, cur)?)),
        Ast::Snd(e) => Ok(format!("Exp.esnd({})", emit_go(e, inf, scope, cur)?)),
    }
}

/// Resolve a name to its de Bruijn index (0 = innermost binder).
fn resolve(scope: &[String], name: &str) -> Result<usize, String> {
    scope
        .iter()
        .rev()
        .position(|n| n == name)
        .ok_or_else(|| format!("unbound variable '{name}'"))
}

/// Render a ground inference type as the object-language `Ty` surface string.
fn emit_ty(t: &Ty) -> String {
    match t {
        Ty::Nat => "Ty.tnat".to_string(),
        Ty::Bool => "Ty.tbool".to_string(),
        Ty::Arrow(a, b) => format!("Ty.tarrow({}, {})", emit_ty(a), emit_ty(b)),
        Ty::Prod(a, b) => format!("Ty.tprod({}, {})", emit_ty(a), emit_ty(b)),
        Ty::Var(_) => unreachable!("emit_ty called on an unresolved type variable"),
    }
}

/// A `Nat` literal as a `succ`/`zero` chain.
fn nat_lit(n: u64) -> String {
    let mut s = String::from("Nat.zero");
    for _ in 0..n {
        s = format!("Nat.succ({})", s);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stlc;

    /// Parse + type-check + run a program written in concrete syntax, end to end.
    fn check_and_run(src: &str, fuel: u64) -> (String, String) {
        let term = parse(src).expect("parse should succeed");
        let mut s = stlc::runnable_session().unwrap();
        s.run(&format!("def prog : Exp := {term}")).unwrap();
        s.run("def prog_ok : Bool := ok(prog)(Ctx.nil)").unwrap();
        s.run(&format!("def prog_val : Exp := run({})(prog)", nat_lit(fuel))).unwrap();
        (s.run_entry("prog_ok").unwrap(), s.run_entry("prog_val").unwrap())
    }

    /// The parser produces a term that elaborates and type-checks (explicit annotations).
    #[test]
    fn parses_and_resolves_names() {
        // `\x:nat. x + 1`  →  λ over de Bruijn 0.
        assert_eq!(
            parse("\\x:nat. x + 1").unwrap(),
            "Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero))))"
        );
        // Nested binders resolve to the right indices: inner `y` = 0, outer `x` = 1.
        assert_eq!(
            parse("\\x:nat. \\y:nat. x + y").unwrap(),
            "Exp.elam(Ty.tnat, Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.succ(Nat.zero)), Exp.evar(Nat.zero))))"
        );
    }

    /// **Type inference**: the SAME programs without annotations infer the identical term.
    #[test]
    fn infers_omitted_annotations() {
        assert_eq!(
            parse("\\x. x + 1").unwrap(),
            "Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero))))"
        );
        assert_eq!(
            parse("\\x. \\y. x + y").unwrap(),
            "Exp.elam(Ty.tnat, Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.succ(Nat.zero)), Exp.evar(Nat.zero))))"
        );
    }

    /// Inference flows a parameter type backwards from a use site: `\f. f true` forces
    /// `f : bool -> ?`, and the application's result var stays free → the body's type is the
    /// only ambiguity. Here we pin it: `\f. if f 0 then 1 else 2` ⇒ `f : nat -> bool`.
    #[test]
    fn infers_higher_order_parameter() {
        assert_eq!(
            parse("\\f. if f 0 then 1 else 2").unwrap(),
            "Exp.elam(Ty.tarrow(Ty.tnat, Ty.tbool), Exp.eif(Exp.eapp(Exp.evar(Nat.zero), Exp.enat(Nat.zero)), Exp.enat(Nat.succ(Nat.zero)), Exp.enat(Nat.succ(Nat.succ(Nat.zero)))))"
        );
    }

    /// **Compile (parse, no annotations) → type-check → run, from text.** A `let`-bound
    /// increment applied twice: `let inc = \x. x + 1 in inc (inc 0)` ⇒ `2`, well typed.
    #[test]
    fn end_to_end_inferred_let_and_application() {
        let (ok, val) = check_and_run("let inc = \\x. x + 1 in inc (inc 0)", 20);
        assert_eq!(ok, "Bool.true", "well typed");
        assert_eq!(val, "Exp.enat 2", "(inc (inc 0)) = 2");
    }

    /// Annotated form still works end to end (backward compatibility).
    #[test]
    fn end_to_end_let_and_application() {
        let (ok, val) = check_and_run("let inc = \\x:nat. x + 1 in inc (inc 0)", 20);
        assert_eq!(ok, "Bool.true", "well typed");
        assert_eq!(val, "Exp.enat 2", "(inc (inc 0)) = 2");
    }

    /// Conditionals + arithmetic from text: `if true then 3 + 4 else 0` ⇒ `7`.
    #[test]
    fn end_to_end_conditional() {
        let (ok, val) = check_and_run("if true then 3 + 4 else 0", 10);
        assert_eq!(ok, "Bool.true");
        assert_eq!(val, "Exp.enat 7");
    }

    /// A higher-order function applied, inferred: `(\f. f (f 1)) (\x. x + 2)` ⇒ `5`.
    #[test]
    fn end_to_end_inferred_higher_order() {
        let (ok, val) = check_and_run("(\\f. f (f 1)) (\\x. x + 2)", 30);
        assert_eq!(ok, "Bool.true");
        assert_eq!(val, "Exp.enat 5");
    }

    /// Ill-typed text is *parsed* fine but *rejected* by the verified checker:
    /// `true + 1` adds a boolean. (Here inference itself catches it first.)
    #[test]
    fn ill_typed_is_rejected() {
        // `true + 1` fails unification (bool ≠ nat) at inference time.
        assert!(parse("true + 1").is_err());
    }

    /// A genuinely ambiguous program (monomorphic identity) is reported, not silently defaulted.
    #[test]
    fn ambiguous_identity_is_reported() {
        let e = parse("\\x. x");
        assert!(e.is_err(), "bare identity has no monomorphic type");
        assert!(e.unwrap_err().contains("ambiguous"));
    }

    /// An unbound name is an error (scope resolution fails during inference).
    #[test]
    fn unbound_variable_is_an_error() {
        assert!(parse("x + 1").is_err());
        assert!(parse("\\x. y").is_err());
    }

    /// **Positioned diagnostics.** A syntax error reports `line:col`, the offending line, and
    /// a caret under the exact column.
    #[test]
    fn syntax_errors_are_positioned() {
        // Missing `in`: after `let x = 1` we want `in`, but hit end of input.
        let e = parse("let x = 1").unwrap_err();
        assert!(e.contains("1:10"), "should point past `1` at col 10: {e}");
        assert!(e.contains("expected `in`"), "names the expected token: {e}");
        assert!(e.contains('^'), "has a caret: {e}");

        // A stray token where an expression atom is expected, on the second line.
        let e2 = parse("1 +\n  )").unwrap_err();
        assert!(e2.contains("2:3"), "points at the `)` on line 2 col 3: {e2}");
        assert!(e2.contains("expected an expression, found `)`"), "{e2}");

        // Unknown character is positioned by the lexer.
        let e3 = parse("1 + @").unwrap_err();
        assert!(e3.contains("1:5") && e3.contains("unexpected character '@'"), "{e3}");
    }

    /// **`let rec` desugars to `let … = fix … in …`.** The recursive binding becomes an
    /// `Exp.efix` whose self-reference and the let body both resolve to de Bruijn 0.
    #[test]
    fn let_rec_desugars_to_fix() {
        // `let rec f : nat = 7 in f`  →  `let f = (fix f. 7) in f`.
        assert_eq!(
            parse("let rec f : nat = 7 in f").unwrap(),
            "Exp.elet(Exp.efix(Ty.tnat, Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))), Exp.evar(Nat.zero))"
        );
    }

    /// **Recursion from text, type inferred, run end to end.** A guarded recursive function
    /// (`let rec f = \x. if true then x+1 else f x in f 5`) infers `f : nat → nat`,
    /// type-checks, and runs to `6` — the recursive call sits in the dead `else` branch.
    #[test]
    fn end_to_end_let_rec_runs() {
        let (ok, val) =
            check_and_run("let rec f = \\x. if true then x + 1 else f x in f 5", 20);
        assert_eq!(ok, "Bool.true", "the recursive function is well typed");
        assert_eq!(val, "Exp.enat 6", "(f 5) = 6 via the guarded recursion");
    }

    /// **Pairs + projections from text, inferred, run end to end.** `fst (1 + 2, true)`
    /// infers `nat` and runs to `3`; `snd (1, false)` infers `bool` and runs to `false`.
    #[test]
    fn end_to_end_products() {
        let (ok1, v1) = check_and_run("fst (1 + 2, true)", 8);
        assert_eq!(ok1, "Bool.true");
        assert_eq!(v1, "Exp.enat 3", "fst (1+2, true) = 3");
        let (ok2, v2) = check_and_run("snd (1, false)", 4);
        assert_eq!(ok2, "Bool.true");
        assert_eq!(v2, "Exp.ebool Bool.false", "snd (1, false) = false");
    }

    /// A λ over a pair, with a product-type annotation: `(\p:nat*bool. fst p) (3, true)` ⇒ `3`.
    #[test]
    fn end_to_end_product_annotation() {
        let (ok, v) = check_and_run("(\\p:nat*bool. fst p) (3, true)", 10);
        assert_eq!(ok, "Bool.true");
        assert_eq!(v, "Exp.enat 3");
    }
}
