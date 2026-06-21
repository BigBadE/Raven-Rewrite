//! Surface syntax: a concrete, named language that elaborates to core terms.
//!
//! The core ([`crate::term`]) uses de Bruijn indices — unwriteable by hand at any
//! scale. This module is the front end: a hand-written lexer + recursive-descent
//! parser producing a *named* AST ([`Expr`], [`Command`]). The [elaborator](crate::elab)
//! turns that into core terms and feeds the [`Kernel`](crate::kernel).
//!
//! ## Grammar (informal)
//!
//! ```text
//! expr    := piTele "->" expr            -- dependent function type
//!          | app "->" expr               -- non-dependent arrow
//!          | app
//! atom    := "(" expr ")"
//!          | "fun" binder+ "=>" expr
//!          | "forall" binder+ "," expr
//!          | "let" ident (":" expr)? ":=" expr "in" expr
//!          | "Type" nat? | "Sort" level | "Prop"
//!          | ident levelArgs?
//! binder  := "(" ident+ ":" expr ")"
//! level   := nat | ident | level "+" nat
//! command := "def" name levelDecl? binder* ":" expr ":=" expr
//!          | "axiom" name levelDecl? binder* ":" expr
//!          | "inductive" name levelDecl? binder* ":" expr ("|" ident ":" expr)*
//!          | "check" expr
//! ```

// ---------------------------------------------------------------------------
// AST
// ---------------------------------------------------------------------------

/// A universe level expression in surface syntax.
#[derive(Clone, Debug, PartialEq)]
pub enum SLevel {
    Nat(u32),
    Var(String),
    Add(Box<SLevel>, u32),
}

/// A binder group `(x y … : T)` (explicit) or `{x y … : T}` (implicit): several
/// names sharing one type. `implicit` binders are *auto-inserted* by the inferring
/// elaborator at call sites (their values are solved by unification), so the caller
/// writes `id(n)` instead of `id(_, n)`.
#[derive(Clone, Debug, PartialEq)]
pub struct Binder {
    pub names: Vec<String>,
    pub ty: Expr,
    pub implicit: bool,
}

/// A surface expression.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Type(u32),
    Prop,
    Sort(SLevel),
    /// A name reference, with optional explicit universe arguments `f.{u, v}`.
    Var(String, Option<Vec<SLevel>>),
    App(Box<Expr>, Box<Expr>),
    Lam(Box<Binder>, Box<Expr>),
    Pi(Box<Binder>, Box<Expr>),
    Arrow(Box<Expr>, Box<Expr>),
    Let(String, Option<Box<Expr>>, Box<Expr>, Box<Expr>),
    /// `a == b` — sugar elaborating to `Eq.{u} T a b` with `T`/`u` inferred from `a`.
    EqOp(Box<Expr>, Box<Expr>),
    /// `match scrut { | C(x…) => body … }` — case analysis, compiled to the scrutinee
    /// inductive's recursor. Structural recursion is available via the per-recursive-
    /// field induction hypothesis, bound as `<field>.rec`.
    Match(Box<Expr>, Vec<MatchArm>),
    /// `_` — a hole, to be solved by inference (a fresh metavariable).
    Hole,
    /// `rewrite h => body` — rewrite the expected type by the equation `h : Eq T a b`
    /// (replacing `a` with `b`), then elaborate `body` against the rewritten goal. Lowers
    /// to `Eq.subst` with a motive abstracted from the expected type. Only valid in a
    /// *checking* position (where an expected type is known).
    Rewrite(Box<Expr>, Box<Expr>),
    /// `decide` — discharge the (decidable) goal by reflection: resolve a `Decidable P`
    /// instance and emit `of_decide_eq_true P inst (refl)`, which the kernel accepts iff
    /// `decide P inst` computes to `true`. Only valid in a checking position.
    Decide,
    /// `by_cases scrut => tbody | fbody` — case-split the *goal* on a `Bool` scrutinee,
    /// refining it (so `match scrut …` reduces in each branch), proving the `true` branch
    /// with `tbody` and the `false` branch with `fbody`. Lowers to `Bool.rec` with a motive
    /// abstracted from the expected type. Only valid in a checking position. This is the
    /// ergonomic fix for pushing a function through a stuck `match`.
    ByCases(Box<Expr>, Box<Expr>, Box<Expr>),
}

/// A `match` pattern: a variable binder (`x`, or `_` for a wildcard) or a constructor
/// applied to sub-patterns (`Expr.add(Expr.lit(m), b)`). Sub-patterns may nest.
#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    /// A binder (or `_` wildcard) matching anything.
    Var(String),
    /// `C(p₀, …, pₖ₋₁)` — a constructor and its sub-patterns (possibly nested).
    Ctor(String, Vec<Pattern>),
}

impl Pattern {
    /// If this is a *flat* pattern `C(x₀, …, xₖ₋₁)` (a constructor whose sub-patterns are
    /// all variables), return the constructor name and the variable names.
    pub fn as_flat(&self) -> Option<(&str, Vec<&str>)> {
        let Pattern::Ctor(c, subs) = self else { return None };
        let vars: Option<Vec<&str>> = subs
            .iter()
            .map(|p| if let Pattern::Var(v) = p { Some(v.as_str()) } else { None })
            .collect();
        vars.map(|vs| (c.as_str(), vs))
    }
    /// Whether this is a flat constructor pattern (the form the recursor compiler takes
    /// directly; anything else is desugared first).
    pub fn is_flat(&self) -> bool {
        self.as_flat().is_some()
    }
}

/// One arm of a `match`: a pattern and its body.
#[derive(Clone, Debug, PartialEq)]
pub struct MatchArm {
    pub pat: Pattern,
    pub body: Expr,
}

/// A top-level command.
#[derive(Clone, Debug, PartialEq)]
pub enum Command {
    Def { name: String, levels: Vec<String>, params: Vec<Binder>, ty: Expr, body: Expr },
    Axiom { name: String, levels: Vec<String>, params: Vec<Binder>, ty: Expr },
    Inductive {
        name: String,
        levels: Vec<String>,
        params: Vec<Binder>,
        result: Expr,
        ctors: Vec<(String, Expr)>,
    },
    Check(Expr),
    /// A specified function. Specs are written as **inline ghost calls** in the body:
    /// `fn name(x: T, …) -> R { requires(P); ensures(Q); <result expr> }`. There may be
    /// any number of `requires(..)`/`ensures(..)` statements; `result` refers to the
    /// returned value inside an `ensures`.
    Fn {
        name: String,
        levels: Vec<String>,
        params: Vec<Binder>,
        ret: Expr,
        requires: Vec<Expr>,
        ensures: Vec<Expr>,
        body: Expr,
    },
    /// Discharge the obligation of a previously-declared `fn`: `prove name := proof`.
    Prove { name: String, proof: Expr },
    /// `instance name : Class args… := body` — a `def` additionally registered in the
    /// instance table (keyed by the head of its result type) for instance resolution.
    Instance { name: String, levels: Vec<String>, params: Vec<Binder>, ty: Expr, body: Expr },
    /// A marker emitted ahead of a `class`'s desugared inductive: registers `name` as a
    /// class so resolution can report a precise "no instance found" for it.
    Class(String),
    /// A `mutual { inductive … inductive … }` block: several inductives declared
    /// simultaneously, able to reference one another. Each element is an
    /// [`Command::Inductive`].
    Mutual(Vec<Command>),
}

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------

/// Tokens, lexed by [`logos`]. The lexer is *untrusted* (the kernel re-checks every
/// elaborated term), so a derive-based lexer here costs nothing in trust — it just
/// removes the fiddliest hand-written code (dotted identifiers vs. the `.{` level
/// bracket, multi-char operators). End-of-input is represented by running off the end
/// of the token vector, not by a token.
#[derive(logos::Logos, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+")] // whitespace
#[logos(skip("--[^\n]*", allow_greedy = true))] // line comments
enum Tok {
    #[regex(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*", |lx| lx.slice().to_owned(), priority = 2)]
    Ident(String),
    #[regex(r"[0-9]+", |lx| lx.slice().parse::<u32>().ok())]
    Nat(u32),
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(":")]
    Colon,
    #[token(":=")]
    ColonEq,
    #[token("=>")]
    FatArrow,
    #[token("->")]
    Arrow,
    #[token("==")]
    EqEq,
    #[token(",")]
    Comma,
    #[token("|")]
    Bar,
    #[token(".{")]
    DotBrace,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("+")]
    Plus,
    #[token("fun")]
    KwFun,
    #[token("forall")]
    KwForall,
    #[token("let")]
    KwLet,
    #[token("in")]
    KwIn,
    #[token("Type")]
    KwType,
    #[token("Sort")]
    KwSort,
    #[token("Prop")]
    KwProp,
    #[token("def")]
    KwDef,
    #[token("axiom")]
    KwAxiom,
    #[token("inductive")]
    KwInductive,
    #[token("check")]
    KwCheck,
    #[token(";")]
    Semi,
    #[token("fn")]
    KwFn,
    #[token("prove")]
    KwProve,
    #[token("match")]
    KwMatch,
    #[token("mutual")]
    KwMutual,
    #[token("calc")]
    KwCalc,
    #[token("rewrite")]
    KwRewrite,
    #[token("structure")]
    KwStructure,
    #[token("where")]
    KwWhere,
    #[token("class")]
    KwClass,
    #[token("instance")]
    KwInstance,
    #[token("by_decide")]
    KwDecide,
    #[token("by_cases")]
    KwByCases,
}

/// Byte offsets where each line begins (line 0 starts at 0). Used to turn a token's byte
/// offset into a human `line:col` for diagnostics.
fn line_starts(src: &str) -> Vec<usize> {
    let mut starts = vec![0usize];
    for (i, b) in src.bytes().enumerate() {
        if b == b'\n' {
            starts.push(i + 1);
        }
    }
    starts
}

/// Convert a byte offset into a 1-based `(line, col)` against precomputed line starts.
fn line_col(starts: &[usize], off: usize) -> (usize, usize) {
    // The line is the last start that is ≤ off.
    let line = match starts.binary_search(&off) {
        Ok(i) => i,
        Err(i) => i - 1,
    };
    (line + 1, off - starts[line] + 1)
}

/// Lex into a token stream paired with each token's source byte-span (for diagnostics).
fn lex(src: &str) -> Result<(Vec<Tok>, Vec<core::ops::Range<usize>>), String> {
    use logos::Logos;
    let mut toks = Vec::new();
    let mut spans = Vec::new();
    let mut lx = Tok::lexer(src);
    while let Some(r) = lx.next() {
        match r {
            Ok(t) => {
                toks.push(t);
                spans.push(lx.span());
            }
            Err(_) => {
                let (l, c) = line_col(&line_starts(src), lx.span().start);
                return Err(format!("{l}:{c}: lex error: unexpected '{}'", lx.slice()));
            }
        }
    }
    Ok((toks, spans))
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

struct Parser {
    toks: Vec<Tok>,
    spans: Vec<core::ops::Range<usize>>,
    line_starts: Vec<usize>,
    src_len: usize,
    pos: usize,
}

impl Parser {
    fn new(toks: Vec<Tok>, spans: Vec<core::ops::Range<usize>>, src: &str) -> Self {
        Self { toks, spans, line_starts: line_starts(src), src_len: src.len(), pos: 0 }
    }
    /// The 1-based `(line, col)` of the current token (or end-of-input).
    fn here_lc(&self) -> (usize, usize) {
        let off = self.spans.get(self.pos).map(|s| s.start).unwrap_or(self.src_len);
        line_col(&self.line_starts, off)
    }
    /// The `line:col` of the current token (or end-of-input), for error prefixes.
    fn here(&self) -> String {
        let (l, c) = self.here_lc();
        format!("{l}:{c}")
    }
    /// Prefix a parse error with the current source position.
    fn err<T>(&self, msg: impl std::fmt::Display) -> Result<T, String> {
        Err(format!("{}: {}", self.here(), msg))
    }
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }
    fn at(&self, t: &Tok) -> bool {
        self.peek() == Some(t)
    }
    fn at_eof(&self) -> bool {
        self.pos >= self.toks.len()
    }
    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.at(t) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    /// Render the current lookahead for a "found X" diagnostic.
    fn found(&self) -> String {
        match self.peek() {
            Some(t) => format!("{t:?}"),
            None => "end of input".to_string(),
        }
    }
    fn expect(&mut self, t: &Tok) -> Result<(), String> {
        if self.eat(t) {
            Ok(())
        } else {
            self.err(format!("expected {t:?}, found {}", self.found()))
        }
    }
    fn ident(&mut self) -> Result<String, String> {
        let found = self.found();
        match self.bump() {
            Some(Tok::Ident(s)) => Ok(s),
            _ => self.err(format!("expected identifier, found {found}")),
        }
    }

    // ----- expressions -----

    fn expr(&mut self) -> Result<Expr, String> {
        // A leading binder group means a dependent Π telescope.
        if self.at_binder_group() {
            let mut binders = Vec::new();
            while self.at_binder_group() {
                binders.push(self.binder()?);
            }
            self.expect(&Tok::Arrow)?;
            let body = self.expr()?;
            return Ok(fold_pi(binders, body));
        }
        let lhs = self.app_eq()?;
        if self.eat(&Tok::Arrow) {
            let rhs = self.expr()?;
            Ok(Expr::Arrow(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    /// An application, optionally followed by `== <application>` (infix equality).
    fn app_eq(&mut self) -> Result<Expr, String> {
        let lhs = self.app()?;
        if self.eat(&Tok::EqEq) {
            let rhs = self.app()?;
            Ok(Expr::EqOp(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    /// Does a binder group `(ident+ :` or `{ident+ :` start here?
    fn at_binder_group(&self) -> bool {
        if !matches!(self.peek(), Some(Tok::LParen) | Some(Tok::LBrace)) {
            return false;
        }
        let mut j = self.pos + 1;
        if !matches!(self.toks.get(j), Some(Tok::Ident(_))) {
            return false;
        }
        while matches!(self.toks.get(j), Some(Tok::Ident(_))) {
            j += 1;
        }
        matches!(self.toks.get(j), Some(Tok::Colon))
    }

    /// Parse a binder group, either explicit `(x y : T)` or implicit `{x y : T}`.
    fn binder(&mut self) -> Result<Binder, String> {
        let (open, close, implicit) = if self.at(&Tok::LBrace) {
            (Tok::LBrace, Tok::RBrace, true)
        } else {
            (Tok::LParen, Tok::RParen, false)
        };
        self.expect(&open)?;
        let mut names = Vec::new();
        while let Some(Tok::Ident(_)) = self.peek() {
            names.push(self.ident()?);
        }
        if names.is_empty() {
            return Err("empty binder group".into());
        }
        self.expect(&Tok::Colon)?;
        let ty = self.expr()?;
        self.expect(&close)?;
        Ok(Binder { names, ty, implicit })
    }

    fn app(&mut self) -> Result<Expr, String> {
        let mut e = self.atom()?;
        loop {
            if self.at(&Tok::LParen) {
                // Rust-like call: `f(a, b, …)` applies `f` to each argument in turn.
                // (A single parenthesized argument `f(a)` is the same as juxtaposition,
                // so existing functional code keeps parsing; only the comma form is new.)
                self.bump();
                if !self.at(&Tok::RParen) {
                    loop {
                        let arg = self.expr()?;
                        e = Expr::App(Box::new(e), Box::new(arg));
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                self.expect(&Tok::RParen)?;
            } else if self.at_atom_start() {
                // Bare juxtaposition `f a b` (the Lean-like core still uses this).
                let arg = self.atom()?;
                e = Expr::App(Box::new(e), Box::new(arg));
            } else {
                break;
            }
        }
        Ok(e)
    }

    fn at_atom_start(&self) -> bool {
        matches!(
            self.peek(),
            Some(
                Tok::LParen
                    | Tok::Ident(_)
                    | Tok::KwType
                    | Tok::KwSort
                    | Tok::KwProp
                    | Tok::KwFun
                    | Tok::KwForall
                    | Tok::KwLet
                    | Tok::KwMatch
                    | Tok::KwCalc
                    | Tok::KwRewrite
                    | Tok::KwDecide
                    | Tok::KwByCases
            )
        )
    }

    /// `by_cases scrut => tbody | fbody`.
    fn by_cases_expr(&mut self) -> Result<Expr, String> {
        self.expect(&Tok::KwByCases)?;
        let scrut = self.app()?;
        self.expect(&Tok::FatArrow)?;
        let tbody = self.expr()?;
        self.expect(&Tok::Bar)?;
        let fbody = self.expr()?;
        Ok(Expr::ByCases(Box::new(scrut), Box::new(tbody), Box::new(fbody)))
    }

    /// `calc a == b := pf1 == c := pf2 …` — an equational chain. Desugars to a
    /// right-nested `Eq.trans _ _ _ _ pfᵢ rest` (all explicit args + the universe inferred),
    /// so a multi-step proof reads top-to-bottom instead of as nested `Eq.trans` calls.
    /// The intermediate right-hand sides are parsed for readability but the proofs alone
    /// determine the term. A proof containing `==`/`->` must be parenthesised.
    fn calc_expr(&mut self) -> Result<Expr, String> {
        self.expect(&Tok::KwCalc)?;
        let _lhs = self.app()?; // starting term — documentation; proofs pin the chain
        let mut proofs = Vec::new();
        while self.eat(&Tok::EqEq) {
            let _rhs = self.app()?; // step target — documentation
            self.expect(&Tok::ColonEq)?;
            proofs.push(self.app()?);
        }
        if proofs.is_empty() {
            return Err("`calc` needs at least one `== <rhs> := <proof>` step".into());
        }
        // Right-fold the proofs through Eq.trans.
        let mut iter = proofs.into_iter().rev();
        let mut acc = iter.next().unwrap();
        for p in iter {
            acc = eq_trans_apply(p, acc);
        }
        Ok(acc)
    }

    /// `rewrite h => body` — rewrite the *goal* by the equation `h : a == b`, replacing `a`
    /// with `b`, then prove the rewritten goal with `body`. Lowers to a `Rewrite` node the
    /// elaborator fills in (it needs the expected type to build the `Eq.subst` motive).
    fn rewrite_expr(&mut self) -> Result<Expr, String> {
        self.expect(&Tok::KwRewrite)?;
        let eqn = self.app()?;
        self.expect(&Tok::FatArrow)?;
        let body = self.expr()?;
        Ok(Expr::Rewrite(Box::new(eqn), Box::new(body)))
    }

    /// Parse `match scrut { | C(x…) => body | … }` (leading `|` optional, arms
    /// separated by `|`, no trailing one). A pattern is a constructor name with an
    /// optional parenthesized list of field binders.
    fn match_expr(&mut self) -> Result<Expr, String> {
        self.expect(&Tok::KwMatch)?;
        let scrut = self.expr()?;
        self.expect(&Tok::LBrace)?;
        let mut arms = Vec::new();
        self.eat(&Tok::Bar); // optional leading bar
        while !self.at(&Tok::RBrace) {
            let pat = self.pattern()?;
            self.expect(&Tok::FatArrow)?;
            let body = self.expr()?;
            arms.push(MatchArm { pat, body });
            if !self.eat(&Tok::Bar) {
                break;
            }
        }
        self.expect(&Tok::RBrace)?;
        Ok(Expr::Match(Box::new(scrut), arms))
    }

    /// Parse a (possibly nested) pattern. A dotted name (`Expr.lit`) is a constructor —
    /// `C(p…)` with sub-patterns, or nullary `C`; an undotted name is a variable binder
    /// (`_` is a wildcard).
    fn pattern(&mut self) -> Result<Pattern, String> {
        let id = self.ident()?;
        if self.eat(&Tok::LParen) {
            let mut subs = Vec::new();
            if !self.at(&Tok::RParen) {
                loop {
                    subs.push(self.pattern()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
            }
            self.expect(&Tok::RParen)?;
            Ok(Pattern::Ctor(id, subs))
        } else if id.contains('.') {
            Ok(Pattern::Ctor(id, Vec::new())) // a nullary constructor (e.g. `Nat.zero`)
        } else {
            Ok(Pattern::Var(id)) // a variable binder (or `_`)
        }
    }

    fn atom(&mut self) -> Result<Expr, String> {
        match self.peek().cloned() {
            Some(Tok::LParen) => {
                self.bump();
                let e = self.expr()?;
                self.expect(&Tok::RParen)?;
                Ok(e)
            }
            Some(Tok::KwType) => {
                self.bump();
                if let Some(Tok::Nat(n)) = self.peek().cloned() {
                    self.bump();
                    Ok(Expr::Type(n))
                } else {
                    Ok(Expr::Type(0))
                }
            }
            Some(Tok::KwProp) => {
                self.bump();
                Ok(Expr::Prop)
            }
            Some(Tok::KwSort) => {
                self.bump();
                Ok(Expr::Sort(self.level()?))
            }
            Some(Tok::KwFun) => {
                self.bump();
                let mut binders = Vec::new();
                while self.at_binder_group() {
                    binders.push(self.binder()?);
                }
                if binders.is_empty() {
                    return Err("`fun` needs at least one (x : T) binder".into());
                }
                self.expect(&Tok::FatArrow)?;
                let body = self.expr()?;
                Ok(fold_lam(binders, body))
            }
            Some(Tok::KwForall) => {
                self.bump();
                let mut binders = Vec::new();
                while self.at_binder_group() {
                    binders.push(self.binder()?);
                }
                if binders.is_empty() {
                    return Err("`forall` needs at least one (x : T) binder".into());
                }
                self.expect(&Tok::Comma)?;
                let body = self.expr()?;
                Ok(fold_pi(binders, body))
            }
            Some(Tok::KwLet) => {
                self.bump();
                let name = self.ident()?;
                let ty = if self.eat(&Tok::Colon) { Some(Box::new(self.expr()?)) } else { None };
                self.expect(&Tok::ColonEq)?;
                let val = self.expr()?;
                self.expect(&Tok::KwIn)?;
                let body = self.expr()?;
                Ok(Expr::Let(name, ty, Box::new(val), Box::new(body)))
            }
            Some(Tok::KwMatch) => self.match_expr(),
            Some(Tok::KwCalc) => self.calc_expr(),
            Some(Tok::KwRewrite) => self.rewrite_expr(),
            Some(Tok::KwDecide) => {
                self.bump();
                Ok(Expr::Decide)
            }
            Some(Tok::KwByCases) => self.by_cases_expr(),
            Some(Tok::Ident(nm)) => {
                self.bump();
                if nm == "_" {
                    return Ok(Expr::Hole); // a hole in expression position
                }
                let levels = if self.at(&Tok::DotBrace) { Some(self.level_args()?) } else { None };
                Ok(Expr::Var(nm, levels))
            }
            _ => self.err(format!("expected an expression, found {}", self.found())),
        }
    }

    fn level_args(&mut self) -> Result<Vec<SLevel>, String> {
        self.expect(&Tok::DotBrace)?;
        let mut ls = Vec::new();
        if !self.at(&Tok::RBrace) {
            ls.push(self.level()?);
            while self.eat(&Tok::Comma) {
                ls.push(self.level()?);
            }
        }
        self.expect(&Tok::RBrace)?;
        Ok(ls)
    }

    fn level(&mut self) -> Result<SLevel, String> {
        let (here, found) = (self.here(), self.found());
        let mut l = match self.bump() {
            Some(Tok::Nat(n)) => SLevel::Nat(n),
            Some(Tok::Ident(s)) => SLevel::Var(s),
            Some(Tok::LParen) => {
                let l = self.level()?;
                self.expect(&Tok::RParen)?;
                l
            }
            _ => return Err(format!("{here}: expected a universe level, found {found}")),
        };
        while self.eat(&Tok::Plus) {
            let (here2, found2) = (self.here(), self.found());
            match self.bump() {
                Some(Tok::Nat(n)) => l = SLevel::Add(Box::new(l), n),
                _ => return Err(format!("{here2}: expected a number after '+', found {found2}")),
            }
        }
        Ok(l)
    }

    // ----- commands -----

    fn level_decl(&mut self) -> Result<Vec<String>, String> {
        if self.at(&Tok::DotBrace) {
            self.bump();
            let mut names = Vec::new();
            if let Some(Tok::Ident(_)) = self.peek() {
                names.push(self.ident()?);
                while self.eat(&Tok::Comma) {
                    names.push(self.ident()?);
                }
            }
            self.expect(&Tok::RBrace)?;
            Ok(names)
        } else {
            Ok(Vec::new())
        }
    }

    fn params(&mut self) -> Result<Vec<Binder>, String> {
        let mut ps = Vec::new();
        while self.at_binder_group() {
            ps.push(self.binder()?);
        }
        Ok(ps)
    }

    fn command(&mut self) -> Result<Command, String> {
        match self.peek().cloned() {
            Some(Tok::KwDef) => {
                self.bump();
                let name = self.ident()?;
                let levels = self.level_decl()?;
                let params = self.params()?;
                self.expect(&Tok::Colon)?;
                let ty = self.expr()?;
                self.expect(&Tok::ColonEq)?;
                let body = self.expr()?;
                Ok(Command::Def { name, levels, params, ty, body })
            }
            Some(Tok::KwAxiom) => {
                self.bump();
                let name = self.ident()?;
                let levels = self.level_decl()?;
                let params = self.params()?;
                self.expect(&Tok::Colon)?;
                let ty = self.expr()?;
                Ok(Command::Axiom { name, levels, params, ty })
            }
            Some(Tok::KwInductive) => {
                self.bump();
                let name = self.ident()?;
                let levels = self.level_decl()?;
                let params = self.params()?;
                self.expect(&Tok::Colon)?;
                let result = self.expr()?;
                let mut ctors = Vec::new();
                while self.eat(&Tok::Bar) {
                    let cname = self.ident()?;
                    self.expect(&Tok::Colon)?;
                    let cty = self.expr()?;
                    ctors.push((cname, cty));
                }
                Ok(Command::Inductive { name, levels, params, result, ctors })
            }
            Some(Tok::KwCheck) => {
                self.bump();
                Ok(Command::Check(self.expr()?))
            }
            Some(Tok::KwMutual) => {
                self.bump();
                self.expect(&Tok::LBrace)?;
                let mut members = Vec::new();
                while !self.at(&Tok::RBrace) {
                    if !self.at(&Tok::KwInductive) {
                        return Err("a `mutual` block may only contain `inductive` \
                                    declarations"
                            .to_string());
                    }
                    members.push(self.command()?);
                }
                self.expect(&Tok::RBrace)?;
                Ok(Command::Mutual(members))
            }
            Some(Tok::KwFn) => {
                self.bump();
                let name = self.ident()?;
                let levels = self.level_decl()?;
                // Optional implicit binder groups `{A : Type}` before the value params;
                // their arguments are auto-inserted at call sites.
                let mut params = Vec::new();
                while self.at(&Tok::LBrace) {
                    params.push(self.binder()?);
                }
                self.expect(&Tok::LParen)?;
                if !self.at(&Tok::RParen) {
                    loop {
                        let pname = self.ident()?;
                        self.expect(&Tok::Colon)?;
                        let pty = self.expr()?;
                        params.push(Binder { names: vec![pname], ty: pty, implicit: false });
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                self.expect(&Tok::RParen)?;
                self.expect(&Tok::Arrow)?;
                let ret = self.expr()?;
                // Body block: zero or more `requires(..)/ensures(..)` statements (each
                // ending in `;`), followed by the result expression.
                self.expect(&Tok::LBrace)?;
                let mut requires = Vec::new();
                let mut ensures = Vec::new();
                let body;
                loop {
                    let e = self.expr()?;
                    if self.eat(&Tok::Semi) {
                        match as_spec_call(&e) {
                            Some((kind, arg)) if kind == "requires" => requires.push(arg),
                            Some((kind, arg)) if kind == "ensures" => ensures.push(arg),
                            _ => {
                                return Err(
                                    "only `requires(..)` and `ensures(..)` statements are \
                                     allowed before the result expression"
                                        .to_string(),
                                )
                            }
                        }
                    } else {
                        body = e;
                        break;
                    }
                }
                self.expect(&Tok::RBrace)?;
                Ok(Command::Fn { name, levels, params, ret, requires, ensures, body })
            }
            Some(Tok::KwProve) => {
                self.bump();
                let name = self.ident()?;
                self.expect(&Tok::ColonEq)?;
                let proof = self.expr()?;
                Ok(Command::Prove { name, proof })
            }
            _ => self.err(format!("expected a command, found {}", self.found())),
        }
    }

    /// Parse one top-level item, which may desugar to **several** commands (a `structure`
    /// expands to an inductive plus one projection `def` per field). Ordinary commands
    /// return a singleton.
    fn item(&mut self) -> Result<Vec<Command>, String> {
        if self.at(&Tok::KwStructure) || self.at(&Tok::KwClass) {
            // A `class` is exactly a single-constructor record; resolution only needs the
            // `instance` table, so a class is structurally identical to a `structure`.
            self.structure()
        } else if self.at(&Tok::KwInstance) {
            Ok(vec![self.instance_cmd()?])
        } else {
            Ok(vec![self.command()?])
        }
    }

    /// `instance name.{ls} (params) : Class args… := body`.
    fn instance_cmd(&mut self) -> Result<Command, String> {
        self.expect(&Tok::KwInstance)?;
        let name = self.ident()?;
        let levels = self.level_decl()?;
        let params = self.params()?;
        self.expect(&Tok::Colon)?;
        let ty = self.expr()?;
        self.expect(&Tok::ColonEq)?;
        let body = self.expr()?;
        Ok(Command::Instance { name, levels, params, ty, body })
    }

    /// `structure Name.{ls} (params) [: SORT] where f1 : T1, f2 : T2, …` — a single-
    /// constructor record. Desugars to `inductive Name … | mk : (f1:T1)→…→Name params`
    /// plus a projection `def Name.fi (params)(self : Name params) : Ti := match self { … }`
    /// for each field. (Fields are non-dependent in this version; the result sort defaults
    /// to `Type 0` if no `: SORT` is given.)
    fn structure(&mut self) -> Result<Vec<Command>, String> {
        let is_class = if self.eat(&Tok::KwStructure) {
            false
        } else {
            self.expect(&Tok::KwClass)?;
            true
        };
        let name = self.ident()?;
        let levels = self.level_decl()?;
        let params = self.params()?;
        let result = if self.eat(&Tok::Colon) { self.expr()? } else { Expr::Type(0) };
        self.expect(&Tok::KwWhere)?;
        // Fields: `f1 : T1, f2 : T2, …` (trailing comma optional).
        let mut fields: Vec<(String, Expr)> = Vec::new();
        loop {
            if !matches!(self.peek(), Some(Tok::Ident(_))) {
                break;
            }
            let fname = self.ident()?;
            self.expect(&Tok::Colon)?;
            let fty = self.expr()?;
            fields.push((fname, fty));
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        if fields.is_empty() {
            return Err("`structure` needs at least one field".into());
        }

        // `Name p…` (the inductive applied to its parameters).
        let applied = apply_params(Expr::Var(name.clone(), None), &params);
        // Constructor `mk : (f1:T1) → … → Name p…`.
        let field_binders: Vec<Binder> = fields
            .iter()
            .map(|(fn_, ft)| Binder { names: vec![fn_.clone()], ty: ft.clone(), implicit: false })
            .collect();
        let ctor_ty = fold_pi(field_binders, applied.clone());
        let inductive = Command::Inductive {
            name: name.clone(),
            levels: levels.clone(),
            params: params.clone(),
            result,
            ctors: vec![("mk".to_string(), ctor_ty)],
        };

        // One projection per field: `def Name.fi (params)(self : Name p…) : Ti :=
        //   match self { Name.mk(x0,…,x_{k-1}) => xi }`.
        let mut out = Vec::new();
        if is_class {
            out.push(Command::Class(name.clone()));
        }
        out.push(inductive);
        let pat_vars: Vec<String> = (0..fields.len()).map(|i| format!("x{i}")).collect();
        for (i, (fname, fty)) in fields.iter().enumerate() {
            let mut proj_params = params.clone();
            proj_params.push(Binder {
                names: vec!["self".to_string()],
                ty: applied.clone(),
                implicit: false,
            });
            let arm = MatchArm {
                pat: Pattern::Ctor(
                    format!("{name}.mk"),
                    pat_vars.iter().map(|v| Pattern::Var(v.clone())).collect(),
                ),
                body: Expr::Var(pat_vars[i].clone(), None),
            };
            let body = Expr::Match(Box::new(Expr::Var("self".to_string(), None)), vec![arm]);
            out.push(Command::Def {
                name: format!("{name}.{fname}"),
                levels: levels.clone(),
                params: proj_params,
                ty: fty.clone(),
                body,
            });
        }
        Ok(out)
    }
}

/// Apply `head` to each parameter variable of a binder telescope (used to write
/// `Name p₀ p₁ …` for a structure/inductive's own type).
fn apply_params(head: Expr, params: &[Binder]) -> Expr {
    let mut e = head;
    for b in params {
        for nm in &b.names {
            e = Expr::App(Box::new(e), Box::new(Expr::Var(nm.clone(), None)));
        }
    }
    e
}

/// Recognize a spec statement `requires(arg)` / `ensures(arg)` — an application of the
/// bare identifier `requires`/`ensures` to one argument. Returns the keyword and the
/// argument expression.
fn as_spec_call(e: &Expr) -> Option<(String, Expr)> {
    if let Expr::App(f, arg) = e {
        if let Expr::Var(n, None) = &**f {
            if n == "requires" || n == "ensures" {
                return Some((n.clone(), (**arg).clone()));
            }
        }
    }
    None
}

/// Build `Eq.trans _ _ _ _ h1 h2` (universe + the four explicit `T a b c` args inferred).
fn eq_trans_apply(h1: Expr, h2: Expr) -> Expr {
    let head = Expr::Var("Eq.trans".to_string(), None);
    let args = [Expr::Hole, Expr::Hole, Expr::Hole, Expr::Hole, h1, h2];
    args.into_iter().fold(head, |f, a| Expr::App(Box::new(f), Box::new(a)))
}

fn fold_pi(binders: Vec<Binder>, body: Expr) -> Expr {
    binders.into_iter().rev().fold(body, |acc, b| Expr::Pi(Box::new(b), Box::new(acc)))
}
fn fold_lam(binders: Vec<Binder>, body: Expr) -> Expr {
    binders.into_iter().rev().fold(body, |acc, b| Expr::Lam(Box::new(b), Box::new(acc)))
}

/// Wrap `body` in a `Π` telescope over `binders` (outermost first).
pub fn pi_telescope(binders: Vec<Binder>, body: Expr) -> Expr {
    fold_pi(binders, body)
}
/// Wrap `body` in a `λ` telescope over `binders` (outermost first).
pub fn lam_telescope(binders: Vec<Binder>, body: Expr) -> Expr {
    fold_lam(binders, body)
}

/// Parse a single expression.
pub fn parse_expr(src: &str) -> Result<Expr, String> {
    let (toks, spans) = lex(src)?;
    let mut p = Parser::new(toks, spans, src);
    let e = p.expr()?;
    if !p.at_eof() {
        return p.err(format!("trailing tokens after expression: {}", p.found()));
    }
    Ok(e)
}

/// Parse a whole program (a sequence of commands).
pub fn parse_program(src: &str) -> Result<Vec<Command>, String> {
    Ok(parse_program_spanned(src)?.into_iter().map(|(c, _)| c).collect())
}

/// Parse a whole program, pairing each command with the 1-based `(line, col)` where it
/// begins. Used by the elaborator to prefix *semantic* errors (type mismatches, failed
/// obligations) with a source position, not just the failing declaration's name. When one
/// item desugars to several commands (e.g. a `structure`), they share its position.
pub fn parse_program_spanned(src: &str) -> Result<Vec<(Command, (usize, usize))>, String> {
    let (toks, spans) = lex(src)?;
    let mut p = Parser::new(toks, spans, src);
    let mut cmds = Vec::new();
    while !p.at_eof() {
        let pos = p.here_lc();
        for c in p.item()? {
            cmds.push((c, pos));
        }
    }
    Ok(cmds)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_basic() {
        let (ts, _spans) = lex("fun (A : Type) => A").unwrap();
        assert_eq!(ts[0], Tok::KwFun);
        assert_eq!(ts[1], Tok::LParen);
        assert_eq!(ts[2], Tok::Ident("A".into()));
    }

    #[test]
    fn parse_errors_carry_line_and_column() {
        // A dangling `(` at column 8 reports its position; the error is `1:9: ...` (the
        // expression is expected at the `)`/EOF right after the open paren).
        let err = parse_expr("foo bar (").unwrap_err();
        assert!(err.starts_with("1:"), "want a line:col prefix, got: {err}");
        assert!(err.contains("expected an expression"), "got: {err}");
    }

    #[test]
    fn line_numbers_track_across_newlines() {
        // The error is on the third line (`def`'s body is missing), so it must say `3:`.
        let src = "def a : Nat := Nat.zero\ndef b : Nat := Nat.zero\ndef c : Nat :=";
        let err = parse_program(src).unwrap_err();
        assert!(err.starts_with("3:"), "want a 3:col prefix, got: {err}");
    }

    #[test]
    fn lex_errors_carry_position() {
        // `#` is not a legal token; the lexer reports its line:col.
        let err = parse_expr("fun x => #").unwrap_err();
        assert!(err.starts_with("1:"), "want a line:col prefix, got: {err}");
        assert!(err.contains("lex error"), "got: {err}");
    }

    #[test]
    fn parse_identity() {
        let e = parse_expr("fun (A : Type) (x : A) => x").unwrap();
        // fun (A:Type) => fun (x:A) => x
        match e {
            Expr::Lam(b, _) => assert_eq!(b.names, vec!["A".to_string()]),
            _ => panic!("expected lambda, got {e:?}"),
        }
    }

    #[test]
    fn parse_dependent_pi() {
        let e = parse_expr("(A : Type) -> A -> A").unwrap();
        assert!(matches!(e, Expr::Pi(_, _)));
    }

    #[test]
    fn parse_dotted_and_levels() {
        let e = parse_expr("Eq.{1} Nat Nat.zero Nat.zero").unwrap();
        // head is Eq.{1}
        fn head(e: &Expr) -> &Expr {
            match e {
                Expr::App(f, _) => head(f),
                other => other,
            }
        }
        match head(&e) {
            Expr::Var(n, Some(ls)) => {
                assert_eq!(n, "Eq");
                assert_eq!(ls, &vec![SLevel::Nat(1)]);
            }
            other => panic!("unexpected head {other:?}"),
        }
    }

    #[test]
    fn parse_rust_like_call() {
        // add(Nat.zero, x)  ==  ((add Nat.zero) x)
        let e = parse_expr("add(Nat.zero, x)").unwrap();
        let expected = parse_expr("add Nat.zero x").unwrap();
        assert_eq!(e, expected);
        // nested calls
        let n = parse_expr("Nat.succ(add(x, y))").unwrap();
        let n2 = parse_expr("Nat.succ (add x y)").unwrap();
        assert_eq!(n, n2);
    }

    #[test]
    fn parse_implicit_binders() {
        // def with an implicit `{A : Type}` param and an explicit `(x : A)`.
        let cmds = parse_program("def idt {A : Type} (x : A) : A := x").unwrap();
        match &cmds[0] {
            Command::Def { params, .. } => {
                assert_eq!(params.len(), 2);
                assert!(params[0].implicit, "first param is implicit");
                assert_eq!(params[0].names, vec!["A".to_string()]);
                assert!(!params[1].implicit, "second param is explicit");
            }
            other => panic!("unexpected {other:?}"),
        }
        // fn with leading implicit group before the value params.
        let cmds = parse_program("fn f {A : Type} (x : A) -> A { x }").unwrap();
        match &cmds[0] {
            Command::Fn { params, .. } => {
                assert_eq!(params.len(), 2);
                assert!(params[0].implicit);
                assert!(!params[1].implicit);
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn parse_match_expression() {
        let e = parse_expr("match n { | Nat.zero => a | Nat.succ(k) => f(k) }").unwrap();
        match e {
            Expr::Match(scrut, arms) => {
                assert!(matches!(*scrut, Expr::Var(ref n, _) if n == "n"));
                assert_eq!(arms.len(), 2);
                assert_eq!(arms[0].pat.as_flat().unwrap(), ("Nat.zero", vec![]));
                assert_eq!(arms[1].pat.as_flat().unwrap(), ("Nat.succ", vec!["k"]));
            }
            other => panic!("expected match, got {other:?}"),
        }
        // A nested pattern parses into nested `Pattern::Ctor`s.
        let n = parse_expr("match e { | Expr.add(Expr.lit(m), b) => m }").unwrap();
        match n {
            Expr::Match(_, arms) => match &arms[0].pat {
                Pattern::Ctor(c, subs) => {
                    assert_eq!(c, "Expr.add");
                    assert!(matches!(&subs[0], Pattern::Ctor(c2, _) if c2 == "Expr.lit"));
                    assert!(matches!(&subs[1], Pattern::Var(v) if v == "b"));
                }
                other => panic!("expected ctor pattern, got {other:?}"),
            },
            other => panic!("expected match, got {other:?}"),
        }
        // Leading `|` is optional; arms are separated by `|`.
        let e2 = parse_expr("match b { Bool.true => x | Bool.false => y }");
        assert!(e2.is_ok(), "leading-bar-optional form should parse: {e2:?}");
    }

    #[test]
    fn parse_mutual_block() {
        let cmds = parse_program(
            "mutual { inductive Tree (A : Type) : Type | node : A -> Forest A -> Tree A \
               inductive Forest (A : Type) : Type | fnil : Forest A }",
        )
        .unwrap();
        match &cmds[0] {
            Command::Mutual(members) => {
                assert_eq!(members.len(), 2);
                assert!(matches!(&members[0], Command::Inductive { name, .. } if name == "Tree"));
                assert!(matches!(&members[1], Command::Inductive { name, .. } if name == "Forest"));
            }
            other => panic!("expected mutual, got {other:?}"),
        }
    }

    #[test]
    fn parse_inductive_command() {
        let cmds =
            parse_program("inductive Nat : Type | zero : Nat | succ : Nat -> Nat").unwrap();
        match &cmds[0] {
            Command::Inductive { name, ctors, .. } => {
                assert_eq!(name, "Nat");
                assert_eq!(ctors.len(), 2);
            }
            other => panic!("unexpected {other:?}"),
        }
    }
}
