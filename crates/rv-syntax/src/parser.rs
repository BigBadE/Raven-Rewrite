//! Recursive-descent parser with precedence climbing for binary operators.
//!
//! Consumes the token stream from [`crate::lexer`] and produces a
//! [`crate::ast::Module`]. All failures are reported as `Err(String)` with a
//! source line, never panics.

use crate::ast::*;
use crate::lexer::{SpannedTok, Tok};
use rv_core::{BinOp, Symbols, UnOp};

/// Parser state: the token buffer plus a cursor.
pub struct Parser<'a> {
    toks: &'a [SpannedTok],
    pos: usize,
    syms: &'a mut Symbols,
    /// When set, an `IDENT {` is NOT treated as a struct literal. This is enabled
    /// while parsing the scrutinee/condition of `if`/`while`/`match`, so that the
    /// `{` there opens the control-flow body rather than a struct literal. (See the
    /// struct-literal-vs-block disambiguation note in the parser docs.)
    no_struct_lit: bool,
}

impl<'a> Parser<'a> {
    pub fn new(toks: &'a [SpannedTok], syms: &'a mut Symbols) -> Self {
        Self { toks, pos: 0, syms, no_struct_lit: false }
    }

    /// Parse `body` with struct literals disabled in expression position (used for
    /// `if`/`while`/`match` conditions), restoring the previous flag afterward.
    fn with_no_struct_lit<T>(
        &mut self,
        body: impl FnOnce(&mut Self) -> Result<T, String>,
    ) -> Result<T, String> {
        let prev = self.no_struct_lit;
        self.no_struct_lit = true;
        let r = body(self);
        self.no_struct_lit = prev;
        r
    }

    /// Parse `body` with struct literals re-enabled (used inside parentheses,
    /// where the `{` ambiguity does not arise), restoring the flag afterward.
    fn with_struct_lit<T>(
        &mut self,
        body: impl FnOnce(&mut Self) -> Result<T, String>,
    ) -> Result<T, String> {
        let prev = self.no_struct_lit;
        self.no_struct_lit = false;
        let r = body(self);
        self.no_struct_lit = prev;
        r
    }

    // ---- low-level token helpers -------------------------------------------

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn line(&self) -> u32 {
        self.toks[self.pos].line
    }

    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].tok.clone();
        // Never advance past Eof.
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }

    /// Consume a token equal to `want` or produce a contextual error.
    fn expect(&mut self, want: &Tok, ctx: &str) -> Result<(), String> {
        if self.peek() == want {
            self.bump();
            Ok(())
        } else {
            Err(format!(
                "line {}: expected {} {ctx}, found {:?}",
                self.line(),
                describe(want),
                self.peek()
            ))
        }
    }

    /// Consume the next token if it equals `want`; report whether it did.
    fn eat(&mut self, want: &Tok) -> bool {
        if self.peek() == want {
            self.bump();
            true
        } else {
            false
        }
    }

    /// Consume a `mut` modifier if present (it lexes as the identifier `mut`).
    /// Returns `true` if a `mut` was consumed. Used for `&mut` borrows / types.
    fn eat_mut(&mut self) -> bool {
        if matches!(self.peek(), Tok::Ident(name) if name == "mut") {
            self.bump();
            true
        } else {
            false
        }
    }

    /// Is the current token the identifier `word`? (Proof-fragment keywords —
    /// `fun`, `Type`, `Prop`, `rewrite`, `decide`, `by_cases`, `forall`, `axiom`,
    /// `def` — are matched by spelling rather than reserved as lexer tokens, so they
    /// stay usable as ordinary identifiers elsewhere.)
    fn peek_kw(&self, word: &str) -> bool {
        matches!(self.peek(), Tok::Ident(n) if n == word)
    }

    /// Consume the identifier `word` if present; report whether it was.
    fn eat_kw(&mut self, word: &str) -> bool {
        if self.peek_kw(word) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// Like [`Self::ident`], but also accepts the `true`/`false` keyword tokens as a
    /// (constructor / variant) name — proof enums such as `enum Bool { false, true }`
    /// reuse those spellings, which the kernel treats as ordinary dotted-name parts.
    fn variant_name(&mut self, ctx: &str) -> Result<rv_core::Sym, String> {
        match self.peek() {
            Tok::True => {
                self.bump();
                Ok(self.syms.intern("true"))
            }
            Tok::False => {
                self.bump();
                Ok(self.syms.intern("false"))
            }
            _ => self.ident(ctx),
        }
    }

    /// Expect an identifier and intern it, returning its `Sym`.
    fn ident(&mut self, ctx: &str) -> Result<rv_core::Sym, String> {
        match self.peek().clone() {
            Tok::Ident(name) => {
                self.bump();
                Ok(self.syms.intern(&name))
            }
            other => Err(format!(
                "line {}: expected identifier {ctx}, found {other:?}",
                self.line()
            )),
        }
    }

    // ---- grammar: program / items ------------------------------------------

    /// `program := (fn_decl | struct_decl | enum_decl | type_alias | trait_decl | impl_decl)*`
    pub fn parse_module(&mut self) -> Result<Module, String> {
        let mut items = Vec::new();
        while self.peek() != &Tok::Eof {
            match self.peek() {
                Tok::Fn => items.push(Item::Fn(self.parse_fn()?)),
                Tok::Struct => items.push(Item::Struct(self.parse_struct()?)),
                Tok::Enum => items.push(Item::Enum(self.parse_enum()?)),
                Tok::Ident(w) if w == "type" => items.push(Item::TypeAlias(self.parse_type_alias()?)),
                Tok::Trait => items.push(Item::Trait(self.parse_trait()?)),
                Tok::Impl => items.push(Item::Impl(self.parse_impl()?)),
                // Proof-fragment items, matched by spelling (no reserved keyword token):
                // `axiom name(..) : T` and `def name(..) : T = e`.
                Tok::Ident(w) if w == "axiom" => items.push(Item::Axiom(self.parse_axiom()?)),
                Tok::Ident(w) if w == "def" => items.push(Item::Def(self.parse_def()?)),
                Tok::Ident(w) if w == "instance" => {
                    items.push(Item::Instance(self.parse_instance()?))
                }
                Tok::Ident(w) if w == "mutual" => items.push(self.parse_mutual()?),
                other => {
                    return Err(format!(
                        "line {}: expected an item (`fn`, `struct`, `enum`, `type`, `trait`, `impl`, \
                         `axiom`, or `def`), found {other:?}",
                        self.line()
                    ))
                }
            }
        }
        Ok(Module { items })
    }

    /// `type_alias := "type" IDENT "=" type "where" expr ";"?`
    fn parse_type_alias(&mut self) -> Result<TypeAliasDecl, String> {
        debug_assert!(self.peek_kw("type"));
        self.bump();
        let name = self.ident("after `type`")?;
        self.expect(&Tok::Eq, "after a type alias name")?;
        let base = self.parse_type()?;
        if !self.eat_kw("where") {
            return Err(format!(
                "line {}: a type alias requires `where <refinement>`",
                self.line()
            ));
        }
        let refinement = self.with_no_struct_lit(|p| p.parse_expr())?;
        self.eat(&Tok::Semi);
        Ok(TypeAliasDecl { name, base, refinement })
    }

    /// `generics := ( "<" generic_param ("," generic_param)* ">" )?`
    /// `generic_param := IDENT ( ":" IDENT ("+" IDENT)* )?`
    ///
    /// Parses an optional generic-parameter list, each parameter with optional
    /// trait bounds. Returns an empty vector when no `<` follows.
    fn parse_generics(&mut self) -> Result<Vec<GenericParam>, String> {
        let mut generics = Vec::new();
        if !self.eat(&Tok::Lt) {
            return Ok(generics);
        }
        loop {
            let name = self.ident("as generic type parameter")?;
            let mut bounds = Vec::new();
            // Optional bounds `: Trait0 + Trait1 + ...`.
            if self.eat(&Tok::Colon) {
                loop {
                    bounds.push(self.ident("as trait bound")?);
                    if !self.eat(&Tok::Plus) {
                        break;
                    }
                }
            }
            generics.push(GenericParam { name, bounds });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::Gt, "to close generic parameters")?;
        Ok(generics)
    }

    /// `struct_decl := "struct" IDENT generics? "{" ( IDENT ":" type ("," ...)* ","? )? "}"`
    fn parse_struct(&mut self) -> Result<StructDecl, String> {
        self.expect(&Tok::Struct, "to start a struct")?;
        let name = self.ident("as struct name")?;
        let generics = self.parse_generics()?;
        self.expect(&Tok::LBrace, "to open struct fields")?;
        let mut fields = Vec::new();
        while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
            let fname = self.ident("as field name")?;
            self.expect(&Tok::Colon, "after field name")?;
            let ty = self.parse_type()?;
            fields.push(FieldDecl { name: fname, ty });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RBrace, "to close struct fields")?;
        Ok(StructDecl { name, generics, fields })
    }

    /// `enum_decl := "enum" IDENT generics? indices? ("->" type)? "{" variant* "}"`
    /// `indices   := "(" IDENT ":" type ("," ...)* ")"`            (relation indices)
    /// `variant   := IDENT field_list? where_clause? ((";"|",")?)`
    /// `field_list:= "(" field ("," field)* ")"`,  `field := (IDENT ":")? type`
    /// `where_clause := "where" IDENT "==" expr ("," ...)*`
    fn parse_enum(&mut self) -> Result<EnumDecl, String> {
        self.expect(&Tok::Enum, "to start an enum")?;
        let name = self.ident("as enum name")?;
        let generics = self.parse_generics()?;
        // Optional GADT index binders `(i0: T0, …)` — these make the enum a relation.
        let mut indices = Vec::new();
        if self.peek() == &Tok::LParen {
            self.bump();
            if self.peek() != &Tok::RParen {
                loop {
                    let iname = self.ident("as relation index name")?;
                    self.expect(&Tok::Colon, "after relation index name")?;
                    let ity = self.parse_type()?;
                    indices.push(Param { name: iname, ty: ity, refinement: None });
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
            }
            self.expect(&Tok::RParen, "after relation indices")?;
        }
        // Optional result sort `-> Prop` / `-> Type`.
        let result_sort = if self.eat(&Tok::Arrow) { Some(self.parse_type()?) } else { None };
        self.expect(&Tok::LBrace, "to open enum variants")?;
        let mut variants = Vec::new();
        while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
            let vname = self.variant_name("as variant name")?;
            let mut field_tys = Vec::new();
            let mut field_names = Vec::new();
            if self.eat(&Tok::LParen) {
                if self.peek() != &Tok::RParen {
                    loop {
                        // A named field `name: Ty` (lookahead `IDENT :`) or a positional `Ty`.
                        let named = matches!(self.peek(), Tok::Ident(_))
                            && self.pos + 1 < self.toks.len()
                            && self.toks[self.pos + 1].tok == Tok::Colon;
                        if named {
                            let fname = self.ident("as field name")?;
                            self.expect(&Tok::Colon, "after field name")?;
                            field_names.push(Some(fname));
                            field_tys.push(self.parse_type()?);
                        } else {
                            field_names.push(None);
                            field_tys.push(self.parse_type()?);
                        }
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                self.expect(&Tok::RParen, "after variant fields")?;
            }
            // Optional `where i == e, …` pinning the conclusion's indices.
            let mut pins = Vec::new();
            if self.eat_kw("where") {
                loop {
                    let iname = self.ident("as a pinned index name")?;
                    self.expect(&Tok::EqEq, "in a `where` index pin")?;
                    let value = self.with_no_struct_lit(|p| p.parse_expr())?;
                    pins.push((iname, value));
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
            }
            variants.push(VariantDecl { name: vname, fields: field_tys, field_names, pins });
            // Variants are separated by `,` or `;` (both optional before `}`).
            let _ = self.eat(&Tok::Comma) || self.eat(&Tok::Semi);
        }
        self.expect(&Tok::RBrace, "to close enum variants")?;
        Ok(EnumDecl { name, generics, indices, result_sort, variants })
    }

    /// `fn_decl := "fn" IDENT generics? "(" params? ")" ("->" type)? clause* block`
    fn parse_fn(&mut self) -> Result<FnDecl, String> {
        self.expect(&Tok::Fn, "to start a function")?;
        let name = self.ident("as function name")?;
        let generics = self.parse_generics()?;
        self.expect(&Tok::LParen, "after function name")?;
        let params = self.parse_params()?;
        self.expect(&Tok::RParen, "after parameters")?;

        let ret = if self.eat(&Tok::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let (requires, ensures) = self.parse_spec_clauses()?;
        let body = self.parse_block()?;
        Ok(FnDecl { name, generics, params, ret, requires, ensures, body })
    }

    /// `axiom_decl := "axiom" IDENT generics? ("(" params? ")")? ":" type`
    /// (proof fragment). The leading `axiom` identifier has not yet been consumed.
    fn parse_axiom(&mut self) -> Result<AxiomDecl, String> {
        self.eat_kw("axiom");
        let name = self.ident("as axiom name")?;
        let generics = self.parse_generics()?;
        let params = if self.eat(&Tok::LParen) {
            let p = self.parse_params()?;
            self.expect(&Tok::RParen, "after axiom parameters")?;
            p
        } else {
            Vec::new()
        };
        self.expect(&Tok::Colon, "before axiom type")?;
        let ty = self.parse_type()?;
        Ok(AxiomDecl { name, generics, params, ty })
    }

    /// `def_decl := "def" IDENT generics? ("(" params? ")")? ":" type "=" expr`
    /// (proof fragment). The leading `def` identifier has not yet been consumed.
    fn parse_def(&mut self) -> Result<DefDecl, String> {
        self.eat_kw("def");
        let name = self.ident("as def name")?;
        let generics = self.parse_generics()?;
        let params = if self.eat(&Tok::LParen) {
            let p = self.parse_params()?;
            self.expect(&Tok::RParen, "after def parameters")?;
            p
        } else {
            Vec::new()
        };
        self.expect(&Tok::Colon, "before def type")?;
        let ty = self.parse_type()?;
        if !self.eat_assign() {
            return Err(format!("line {}: expected `:=` or `=` before def body", self.line()));
        }
        let body = self.parse_expr()?;
        Ok(DefDecl { name, generics, params, ty, body })
    }

    /// `instance_decl := "instance" IDENT generics? ("(" params? ")")? ":" type ":=" expr`.
    fn parse_instance(&mut self) -> Result<DefDecl, String> {
        self.eat_kw("instance");
        let name = self.ident("as instance name")?;
        let generics = self.parse_generics()?;
        let params = if self.eat(&Tok::LParen) {
            let p = self.parse_params()?;
            self.expect(&Tok::RParen, "after instance parameters")?;
            p
        } else {
            Vec::new()
        };
        self.expect(&Tok::Colon, "before instance type")?;
        let ty = self.parse_type()?;
        if !self.eat_assign() {
            return Err(format!("line {}: expected `:=` or `=` before instance body", self.line()));
        }
        let body = self.parse_expr()?;
        Ok(DefDecl { name, generics, params, ty, body })
    }

    /// `mutual_block := "mutual" "{" enum_decl* "}"` — mutually-referential inductives.
    fn parse_mutual(&mut self) -> Result<Item, String> {
        self.eat_kw("mutual");
        self.expect(&Tok::LBrace, "to open a mutual block")?;
        let mut enums = Vec::new();
        while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
            if self.peek() != &Tok::Enum {
                return Err(format!(
                    "line {}: a `mutual` block may only contain `enum` declarations, found {:?}",
                    self.line(),
                    self.peek()
                ));
            }
            enums.push(self.parse_enum()?);
        }
        self.expect(&Tok::RBrace, "to close a mutual block")?;
        Ok(Item::Mutual(enums))
    }

    /// `clause* := ("requires" expr ";" | "ensures" expr ";")*` in any order.
    /// Shared by `fn` declarations and `impl` methods.
    fn parse_spec_clauses(&mut self) -> Result<(Vec<Expr>, Vec<Expr>), String> {
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        loop {
            if self.eat(&Tok::Requires) {
                let e = self.parse_expr()?;
                self.expect(&Tok::Semi, "after requires clause")?;
                requires.push(e);
            } else if self.eat(&Tok::Ensures) {
                let e = self.parse_expr()?;
                self.expect(&Tok::Semi, "after ensures clause")?;
                ensures.push(e);
            } else {
                break;
            }
        }
        Ok((requires, ensures))
    }

    /// `trait_decl := "trait" IDENT "{" trait_method_sig* "}"`
    /// `trait_method_sig := "fn" IDENT "(" ["self" ("," params)? | params] ")" ("->" type)? ";"`
    fn parse_trait(&mut self) -> Result<TraitDecl, String> {
        self.expect(&Tok::Trait, "to start a trait")?;
        let name = self.ident("as trait name")?;
        self.expect(&Tok::LBrace, "to open trait body")?;
        let mut methods = Vec::new();
        while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
            self.expect(&Tok::Fn, "to start a trait method signature")?;
            let mname = self.ident("as trait method name")?;
            self.expect(&Tok::LParen, "after trait method name")?;
            let (has_self, params) = self.parse_method_params()?;
            self.expect(&Tok::RParen, "after trait method parameters")?;
            let ret = if self.eat(&Tok::Arrow) { Some(self.parse_type()?) } else { None };
            self.expect(&Tok::Semi, "after trait method signature")?;
            methods.push(TraitMethodSig { name: mname, has_self, params, ret });
        }
        self.expect(&Tok::RBrace, "to close trait body")?;
        Ok(TraitDecl { name, methods })
    }

    /// `impl_decl := "impl" IDENT ("for" IDENT)? "{" method* "}"`
    ///
    /// `impl Type { ... }` is inherent; `impl Trait for Type { ... }` is a trait
    /// impl (the leading name is the trait, the post-`for` name is the type).
    fn parse_impl(&mut self) -> Result<ImplDecl, String> {
        self.expect(&Tok::Impl, "to start an impl block")?;
        let first = self.ident("as impl type or trait name")?;
        // `impl Trait for Type` vs inherent `impl Type`.
        let (trait_name, type_name) = if self.eat(&Tok::For) {
            let ty = self.ident("as impl target type")?;
            (Some(first), ty)
        } else {
            (None, first)
        };
        self.expect(&Tok::LBrace, "to open impl body")?;
        let mut methods = Vec::new();
        while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
            methods.push(self.parse_method()?);
        }
        self.expect(&Tok::RBrace, "to close impl body")?;
        Ok(ImplDecl { trait_name, type_name, methods })
    }

    /// `method := "fn" IDENT generics? "(" ["self" ("," params)? | params] ")"
    ///            ("->" type)? clause* block`
    fn parse_method(&mut self) -> Result<MethodDecl, String> {
        self.expect(&Tok::Fn, "to start a method")?;
        let name = self.ident("as method name")?;
        let generics = self.parse_generics()?;
        self.expect(&Tok::LParen, "after method name")?;
        let (has_self, params) = self.parse_method_params()?;
        self.expect(&Tok::RParen, "after method parameters")?;
        let ret = if self.eat(&Tok::Arrow) { Some(self.parse_type()?) } else { None };
        let (requires, ensures) = self.parse_spec_clauses()?;
        let body = self.parse_block()?;
        Ok(MethodDecl { name, generics, has_self, params, ret, requires, ensures, body })
    }

    /// Parse a method's parameter list: an optional leading `self` receiver,
    /// followed by ordinary `name: ty` parameters. Returns `(has_self, params)`.
    /// `self` lexes as an ordinary identifier, so we match on its spelling.
    fn parse_method_params(&mut self) -> Result<(bool, Vec<Param>), String> {
        let mut has_self = false;
        if matches!(self.peek(), Tok::Ident(name) if name == "self") {
            self.bump();
            has_self = true;
            // A `self` receiver may be followed by `,` then ordinary params.
            if !self.eat(&Tok::Comma) {
                return Ok((has_self, Vec::new()));
            }
        }
        // Remaining ordinary parameters (possibly none).
        let params = self.parse_params()?;
        Ok((has_self, params))
    }

    /// `params := param ("," param)*` (possibly empty; handled by caller's `)`).
    fn parse_params(&mut self) -> Result<Vec<Param>, String> {
        let mut params = Vec::new();
        if self.peek() == &Tok::RParen {
            return Ok(params);
        }
        loop {
            let name = self.ident("as parameter name")?;
            self.expect(&Tok::Colon, "after parameter name")?;
            let ty = self.parse_type()?;
            // An optional refinement `where p` (a precondition on this parameter).
            let refinement = if self.eat_kw("where") {
                Some(self.with_no_struct_lit(|p| p.parse_expr())?)
            } else {
                None
            };
            params.push(Param { name, ty, refinement });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        Ok(params)
    }

    /// `type := "&" "mut"? type | scalar | "()" | IDENT generic? | type_expr`
    ///
    /// Executable types (`i64`, `f64`, `bool`, `String`, `()`, `&mut T`, `Option<i64>`) parse exactly as
    /// before. In the **proof fragment** a type position may instead hold a dependent
    /// type-expression — a proposition `a == b`, a function type `A -> B`, a universe
    /// `Type`/`Prop`, or a type-level application `Eval(env, e, v)` — which is captured as
    /// [`Ty::Term`]. The two are distinguished purely by what follows the base type:
    /// executable types are never followed by `(`, `==`, or `->`.
    fn parse_type(&mut self) -> Result<Ty, String> {
        // Universes (`Type`, `Type n`, `Prop`) — proof fragment, matched by spelling.
        if self.peek_kw("Type") {
            self.bump();
            let n = if let Tok::Int(n) = self.peek().clone() {
                self.bump();
                n as u32
            } else {
                0
            };
            return self.type_expr_tail(Expr::TypeUniv(n));
        }
        if self.peek_kw("Prop") {
            self.bump();
            return self.type_expr_tail(Expr::Prop);
        }
        // Reference type: `&T` or `&mut T`. `mut` arrives from the lexer as an
        // ordinary identifier, so we test its spelling rather than a keyword token.
        if self.eat(&Tok::Amp) {
            let mutable = self.eat_mut();
            let inner = self.parse_type()?;
            return Ok(Ty::Ref { mutable, inner: Box::new(inner) });
        }
        // A parenthesized type may be `()` (unit), a dependent binder group
        // `(x y : T) -> rest` (a `Pi`/`forall` type), a grouped type, or — proof fragment —
        // a function type written in parens `(Nat -> Option<A>)`.
        if self.peek() == &Tok::LParen {
            self.bump();
            if self.eat(&Tok::RParen) {
                return Ok(Ty::Unit);
            }
            // Detect a dependent binder group: `( IDENT+ : … )`.
            let mut j = self.pos;
            while matches!(self.toks.get(j).map(|t| &t.tok), Some(Tok::Ident(_))) {
                j += 1;
            }
            if j > self.pos && self.toks.get(j).map(|t| &t.tok) == Some(&Tok::Colon) {
                // `(x y … : T) -> rest` → a dependent function type binding x, y, … : T,
                // optionally graded `(x :1 T) -> rest` / `(x :0 T) -> rest` (a QTT usage
                // grade shared by every name in the group — see
                // `Self::parse_binder_grade`). This is the working spelling for a `Π`/
                // `forall` type in a *type position* (`def f(..) : (x :1 T) -> U := ..`);
                // the `forall x : T, body` keyword form is the equivalent for expression
                // position (inside a body), parsed by `Self::parse_forall`.
                let mut names = Vec::new();
                while matches!(self.peek(), Tok::Ident(_)) {
                    names.push(self.ident("as a dependent binder name")?);
                }
                self.expect(&Tok::Colon, "in a dependent binder group")?;
                let grade = self.parse_binder_grade();
                let bty = self.parse_type()?;
                self.expect(&Tok::RParen, "after a dependent binder group")?;
                self.expect(&Tok::Arrow, "after a dependent binder `(x : T)`")?;
                let bty_e = self.ty_to_expr(bty)?;
                let bty_e = self.apply_grade_marker(grade, bty_e);
                let rest = self.parse_type()?;
                let body = self.ty_to_expr(rest)?;
                let params = names.into_iter().map(|n| (n, Box::new(bty_e.clone()))).collect();
                return Ok(Ty::Term(Box::new(Expr::Forall { params, body: Box::new(body) })));
            }
            let inner = self.parse_type()?;
            self.expect(&Tok::RParen, "to close a parenthesized type")?;
            // A `->`/`==`/application after the closing paren continues a type-expression.
            return if matches!(self.peek(), Tok::Arrow | Tok::EqEq | Tok::LParen) {
                let e = self.ty_to_expr(inner)?;
                self.type_expr_tail(e)
            } else {
                Ok(inner)
            };
        }
        let base = match self.peek().clone() {
            // Primitive types arrive as identifiers from the lexer.
            Tok::Ident(name) if name == "i64" => {
                self.bump();
                Ty::I64
            }
            Tok::Ident(name) if fixed_int_ty(&name).is_some() => {
                self.bump();
                Ty::IntN(fixed_int_ty(&name).expect("guarded above"))
            }
            Tok::Ident(name) if name == "f64" => {
                self.bump();
                Ty::F64
            }
            Tok::Ident(name) if name == "bool" => {
                self.bump();
                Ty::Bool
            }
            Tok::Ident(name) if name == "String" => {
                self.bump();
                Ty::String
            }
            // Any other identifier names a user-defined struct/enum, an optional
            // generic application (`Base<arg, ...>`), or — resolved at lowering —
            // a bare type parameter.
            Tok::Ident(name) => {
                self.bump();
                let base = self.syms.intern(&name);
                // A `::` makes this a constructor-path *value* used in a type-expression
                // (a proposition like `Nat::Zero == Nat::Succ(b)`): parse the ctor and
                // continue as a type-expression.
                if self.peek() == &Tok::ColonColon {
                    self.bump();
                    let variant = self.variant_name("as enum variant in a type")?;
                    let args = if self.eat(&Tok::LParen) {
                        let a = self.parse_args()?;
                        self.expect(&Tok::RParen, "after enum constructor arguments")?;
                        a
                    } else {
                        Vec::new()
                    };
                    let e = Expr::EnumCtor { enum_name: base, variant, args };
                    return self.type_expr_tail(e);
                }
                // A `<` immediately after the name opens a generic argument list.
                if self.eat(&Tok::Lt) {
                    let mut args = Vec::new();
                    loop {
                        args.push(self.parse_type()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(&Tok::Gt, "to close generic type arguments")?;
                    Ty::Generic { base, args }
                } else {
                    Ty::Adt(base)
                }
            }
            other => {
                return Err(format!(
                    "line {}: expected a type (`i64`, `f64`, `bool`, `String`, `()`, or a type name), found {other:?}",
                    self.line()
                ))
            }
        };
        // Proof continuation: a `(`/`==`/`->` or a juxtaposed atom (`native_add a b`) turns
        // the base into a type-expression.
        if matches!(self.peek(), Tok::LParen | Tok::EqEq | Tok::Arrow) || self.is_juxt_atom_start()
        {
            let e = self.ty_to_expr(base)?;
            return self.type_expr_tail(e);
        }
        Ok(base)
    }

    /// Convert an already-parsed simple [`Ty`] back into the equivalent proof-fragment
    /// [`Expr`], so a type-expression continuation (`== …`, `-> …`, application) can be
    /// parsed on top of it. Only the forms reachable in the proof fragment are handled.
    fn ty_to_expr(&mut self, ty: Ty) -> Result<Expr, String> {
        Ok(match ty {
            Ty::Adt(s) | Ty::Param(s) => Expr::Var(s),
            Ty::Generic { base, args } => {
                // `Base<a, b>` as a type-level application `Base a b`.
                let mut callee = Expr::Var(base);
                let mut eargs = Vec::new();
                for a in args {
                    eargs.push(self.ty_to_expr(a)?);
                }
                callee = Expr::Apply { callee: Box::new(callee), args: eargs };
                callee
            }
            Ty::Term(e) => *e,
            other => {
                return Err(format!(
                    "line {}: this type cannot appear in a dependent type-expression: {other:?}",
                    self.line()
                ))
            }
        })
    }

    /// Parse the tail of a proof type-expression whose head `lhs` is already in hand: an
    /// application spine (paren-applications `(args)` and ML-style juxtaposition `f a b`),
    /// then an optional `== rhs`, then an optional right-associative arrow `-> rest`.
    /// Returns the whole thing as [`Ty::Term`].
    fn type_expr_tail(&mut self, lhs: Expr) -> Result<Ty, String> {
        let mut lhs = self.parse_app_spine(lhs)?;
        // Equality proposition `a == b` (the `b` is itself an application spine). Struct
        // literals are disabled so a following `{` opens the function body, not a struct lit.
        if self.eat(&Tok::EqEq) {
            let rhs_head = self.with_no_struct_lit(|p| p.parse_unary())?;
            let rhs = self.parse_app_spine(rhs_head)?;
            lhs = Expr::Bin(BinOp::Eq, Box::new(lhs), Box::new(rhs));
        }
        // Right-associative function arrow `A -> B`.
        if self.eat(&Tok::Arrow) {
            let rhs = self.parse_type()?;
            let rhs_e = self.ty_to_expr(rhs)?;
            lhs = Expr::Arrow(Box::new(lhs), Box::new(rhs_e));
        }
        Ok(Ty::Term(Box::new(lhs)))
    }

    /// Parse an application spine onto `head`: paren-applications `head(a, …)` (chained
    /// `head(a)(b)`) and ML-style juxtaposition `head a b` (proof fragment — e.g. an `axiom`
    /// type `native_add a b == plus a b`).
    fn parse_app_spine(&mut self, mut head: Expr) -> Result<Expr, String> {
        loop {
            if self.peek() == &Tok::LParen {
                self.bump();
                let args = self.parse_args()?;
                self.expect(&Tok::RParen, "after type-level application arguments")?;
                head = Expr::Apply { callee: Box::new(head), args };
            } else if self.is_juxt_atom_start() {
                let atom = self.parse_juxt_atom()?;
                head = Expr::Apply { callee: Box::new(head), args: vec![atom] };
            } else {
                break;
            }
        }
        Ok(head)
    }

    /// Does the current token start a juxtaposition argument (an identifier that is not a
    /// contextual keyword)? Used only inside proof type-expressions.
    fn is_juxt_atom_start(&self) -> bool {
        matches!(self.peek(), Tok::Ident(n)
            if !matches!(n.as_str(),
                "where" | "in" | "fun" | "forall" | "Type" | "Prop"
                | "by_decide" | "rewrite" | "by_cases" | "mut"
                // item-level keywords end the spine (the next declaration begins)
                | "axiom" | "def" | "instance" | "mutual"))
    }

    /// Parse a single juxtaposition argument: an identifier `x` or a constructor path
    /// `Enum::Variant(args?)`.
    fn parse_juxt_atom(&mut self) -> Result<Expr, String> {
        let s = self.ident("as a juxtaposed argument")?;
        if self.eat(&Tok::ColonColon) {
            let variant = self.variant_name("as enum variant in a juxtaposed argument")?;
            let args = if self.eat(&Tok::LParen) {
                let a = self.parse_args()?;
                self.expect(&Tok::RParen, "after enum constructor arguments")?;
                a
            } else {
                Vec::new()
            };
            Ok(Expr::EnumCtor { enum_name: s, variant, args })
        } else {
            Ok(Expr::Var(s))
        }
    }

    // ---- grammar: statements / blocks --------------------------------------

    /// `block := "{" stmt* "}"`
    fn parse_block(&mut self) -> Result<Block, String> {
        self.expect(&Tok::LBrace, "to open a block")?;
        let mut stmts = Vec::new();
        while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
            stmts.push(self.parse_stmt()?);
        }
        self.expect(&Tok::RBrace, "to close a block")?;
        Ok(Block { stmts })
    }

    fn parse_stmt(&mut self) -> Result<Stmt, String> {
        match self.peek() {
            Tok::Let => self.parse_let(),
            Tok::If => self.parse_if(),
            Tok::While => self.parse_while(),
            // A proof-style `match` (arms led by `|`, expression bodies) is the
            // value-producing tail of a functional body; parse it as an expression and
            // treat it as an implicit return. An executable `match` (block arms) stays a
            // statement.
            Tok::Match if self.match_is_expr() => {
                let e = self.parse_match_expr()?;
                Ok(Stmt::Return(Some(e)))
            }
            Tok::Match => self.parse_match(),
            Tok::Return => self.parse_return(),
            Tok::Assert => self.parse_assert(),
            Tok::Panic => self.parse_panic(),
            // Either an assignment `IDENT = ...;` or a bare expression `expr;`.
            // A leading identifier followed by `=` is an assignment; otherwise
            // it is an expression statement.
            Tok::Ident(_) if self.peek_is_assignment() => self.parse_assign(),
            _ => {
                let e = self.parse_expr()?;
                // A `*place = value;` store-through-a-reference: the parsed
                // expression is the assignment target and `=` follows. (Plain
                // `IDENT = ...` is handled above; this covers deref targets.)
                if self.eat(&Tok::Eq) {
                    let value = self.parse_expr()?;
                    self.expect(&Tok::Semi, "after assignment")?;
                    return Ok(Stmt::DerefAssign { place: e, value });
                }
                // A trailing expression with no `;` before the closing `}` is the block's
                // *tail* (Rust-style implicit return) — the form functional/proof bodies
                // use (`fn two() -> Nat { Nat::Succ(Nat::Zero) }`).
                if self.peek() == &Tok::RBrace {
                    return Ok(Stmt::Return(Some(e)));
                }
                self.expect(&Tok::Semi, "after expression statement")?;
                Ok(Stmt::Expr(e))
            }
        }
    }

    /// Lookahead at a `match`: do its arms begin with `|` (the proof/expression form)?
    /// The scrutinee is parsed with struct literals disabled, so the first `{` after
    /// `match` opens the arm list; we then check whether a `|` leads the arms.
    fn match_is_expr(&self) -> bool {
        let mut i = self.pos + 1; // skip `match`
        while i < self.toks.len() {
            match self.toks[i].tok {
                // A `|`-led arm list is the proof/expression form; an *empty* `match s { }`
                // is an absurd elimination, also an expression (executable matches are
                // never empty).
                Tok::LBrace => {
                    return matches!(
                        self.toks.get(i + 1).map(|t| &t.tok),
                        Some(Tok::Pipe) | Some(Tok::RBrace)
                    )
                }
                Tok::Eof => return false,
                _ => i += 1,
            }
        }
        false
    }

    /// Lookahead: is the current `IDENT` immediately followed by a `=` (and not
    /// `==`)? Used to disambiguate assignment from an expression statement.
    fn peek_is_assignment(&self) -> bool {
        matches!(self.peek(), Tok::Ident(_))
            && self.pos + 1 < self.toks.len()
            && self.toks[self.pos + 1].tok == Tok::Eq
    }

    /// `"let" IDENT (":" type)? "=" expr ";"` (executable statement) — or, in the proof
    /// fragment, a let-*expression* `"let" IDENT (":" type)? ":=" expr "in" expr` (the whole
    /// body's tail). The two are told apart by the assignment operator: `=` is a statement,
    /// `:=` a proof let-expression.
    fn parse_let(&mut self) -> Result<Stmt, String> {
        self.expect(&Tok::Let, "to start a let binding")?;
        let name = self.ident("as let binding name")?;
        // A `:` that is *not* the start of `:=` introduces a type annotation.
        let has_ann = self.peek() == &Tok::Colon
            && self.toks.get(self.pos + 1).map(|t| &t.tok) != Some(&Tok::Eq);
        let ty = if has_ann {
            self.bump();
            Some(self.parse_type()?)
        } else {
            None
        };
        // Proof let-expression: `:= init in body`.
        if self.peek() == &Tok::Colon
            && self.toks.get(self.pos + 1).map(|t| &t.tok) == Some(&Tok::Eq)
        {
            self.bump();
            self.bump(); // consume `:=`
            let init = self.parse_expr()?;
            self.expect_kw("in", "after a `let … :=` proof binding")?;
            let body = self.parse_expr()?;
            let ty_e = ty.map(|t| self.ty_to_expr(t)).transpose()?;
            return Ok(Stmt::Return(Some(Expr::LetIn {
                name,
                ty: ty_e.map(Box::new),
                init: Box::new(init),
                body: Box::new(body),
            })));
        }
        self.expect(&Tok::Eq, "in let binding")?;
        let init = self.parse_expr()?;
        self.expect(&Tok::Semi, "after let binding")?;
        Ok(Stmt::Let { name, ty, init })
    }

    /// A let-*expression* in expression position: `let x (: T)? := init in body`.
    fn parse_let_in_expr(&mut self) -> Result<Expr, String> {
        self.expect(&Tok::Let, "to start a let-expression")?;
        let name = self.ident("as let-expression binding name")?;
        let has_ann = self.peek() == &Tok::Colon
            && self.toks.get(self.pos + 1).map(|t| &t.tok) != Some(&Tok::Eq);
        let ty = if has_ann {
            self.bump();
            Some(Box::new(self.ty_to_expr_via_type()?))
        } else {
            None
        };
        if !self.eat_assign() {
            return Err(format!("line {}: expected `:=` or `=` in a let-expression", self.line()));
        }
        let init = self.parse_expr()?;
        self.expect_kw("in", "after a `let … :=` binding")?;
        let body = self.parse_expr()?;
        Ok(Expr::LetIn { name, ty, init: Box::new(init), body: Box::new(body) })
    }

    /// Parse a type and immediately convert it to the equivalent proof-fragment expression.
    fn ty_to_expr_via_type(&mut self) -> Result<Expr, String> {
        let t = self.parse_type()?;
        self.ty_to_expr(t)
    }

    /// Consume an assignment operator `:=` (proof) or `=` (executable); report success.
    fn eat_assign(&mut self) -> bool {
        if self.peek() == &Tok::Colon
            && self.toks.get(self.pos + 1).map(|t| &t.tok) == Some(&Tok::Eq)
        {
            self.bump();
            self.bump();
            true
        } else if self.peek() == &Tok::Eq {
            self.bump();
            true
        } else {
            false
        }
    }

    /// Expect the contextual keyword identifier `word`.
    fn expect_kw(&mut self, word: &str, ctx: &str) -> Result<(), String> {
        if self.eat_kw(word) {
            Ok(())
        } else {
            Err(format!("line {}: expected `{word}` {ctx}, found {:?}", self.line(), self.peek()))
        }
    }

    /// `IDENT "=" expr ";"`
    fn parse_assign(&mut self) -> Result<Stmt, String> {
        let name = self.ident("as assignment target")?;
        self.expect(&Tok::Eq, "in assignment")?;
        let value = self.parse_expr()?;
        self.expect(&Tok::Semi, "after assignment")?;
        Ok(Stmt::Assign { name, value })
    }

    /// `"if" expr block ("else" block)?`
    ///
    /// The condition is parsed with struct literals disabled so that the `{`
    /// following it opens the `then` block, not a struct literal.
    fn parse_if(&mut self) -> Result<Stmt, String> {
        self.expect(&Tok::If, "to start an if statement")?;
        let cond = self.with_no_struct_lit(|p| p.parse_expr())?;
        let then_blk = self.parse_block()?;
        let else_blk = if self.eat(&Tok::Else) {
            Some(self.parse_block()?)
        } else {
            None
        };
        Ok(Stmt::If { cond, then_blk, else_blk })
    }

    /// `"while" expr ("invariant" expr ";")* block`
    ///
    /// The condition is parsed with struct literals disabled (so the body `{`
    /// is not mistaken for a struct literal); zero or more `invariant` clauses
    /// may then precede the body.
    fn parse_while(&mut self) -> Result<Stmt, String> {
        self.expect(&Tok::While, "to start a while loop")?;
        let cond = self.with_no_struct_lit(|p| p.parse_expr())?;
        // Zero or more `invariant <expr>;` clauses before the body.
        let mut invariants = Vec::new();
        while self.eat(&Tok::Invariant) {
            let inv = self.with_no_struct_lit(|p| p.parse_expr())?;
            self.expect(&Tok::Semi, "after invariant clause")?;
            invariants.push(inv);
        }
        let body = self.parse_block()?;
        Ok(Stmt::While { cond, invariants, body })
    }

    /// `"match" expr "{" arm* "}"` where `arm := pattern "=>" block ","?`
    fn parse_match(&mut self) -> Result<Stmt, String> {
        self.expect(&Tok::Match, "to start a match")?;
        let scrut = self.with_no_struct_lit(|p| p.parse_expr())?;
        self.expect(&Tok::LBrace, "to open match arms")?;
        let mut arms = Vec::new();
        while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
            let pat = self.parse_pattern()?;
            self.expect(&Tok::FatArrow, "after match pattern")?;
            let body = self.parse_block()?;
            arms.push(MatchArm { pat, body });
            // Arms may optionally be comma-separated.
            self.eat(&Tok::Comma);
        }
        self.expect(&Tok::RBrace, "to close match arms")?;
        Ok(Stmt::Match { scrut, arms })
    }

    /// `pattern := IDENT "::" IDENT ( "(" patbind ("," patbind)* ")" )? | "_"`
    /// `patbind := IDENT | "_"`
    fn parse_pattern(&mut self) -> Result<Pattern, String> {
        // The wildcard pattern is the identifier `_`.
        if let Tok::Ident(name) = self.peek() {
            if name == "_" {
                self.bump();
                return Ok(Pattern::Wildcard);
            }
        }
        let enum_name = self.ident("as enum name in pattern")?;
        self.expect(&Tok::ColonColon, "between enum and variant in pattern")?;
        let variant = self.variant_name("as variant name in pattern")?;
        let mut binds = Vec::new();
        if self.eat(&Tok::LParen) {
            loop {
                binds.push(self.parse_patbind()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::RParen, "after pattern binders")?;
        }
        Ok(Pattern::Variant { enum_name, variant, binds })
    }

    /// A single pattern binder: a name to bind, or `_` to ignore.
    fn parse_patbind(&mut self) -> Result<PatBind, String> {
        let name = self.ident("as pattern binder")?;
        if self.syms.resolve(name) == "_" {
            Ok(PatBind::Wildcard)
        } else {
            Ok(PatBind::Name(name))
        }
    }

    /// `"return" expr? ";"`
    fn parse_return(&mut self) -> Result<Stmt, String> {
        self.expect(&Tok::Return, "to start a return")?;
        if self.eat(&Tok::Semi) {
            return Ok(Stmt::Return(None));
        }
        let e = self.parse_expr()?;
        self.expect(&Tok::Semi, "after return value")?;
        Ok(Stmt::Return(Some(e)))
    }

    /// `"assert" expr ";"`
    fn parse_assert(&mut self) -> Result<Stmt, String> {
        self.expect(&Tok::Assert, "to start an assert")?;
        let e = self.parse_expr()?;
        self.expect(&Tok::Semi, "after assert")?;
        Ok(Stmt::Assert(e))
    }

    /// `"panic" ( "(" expr ")" )? ";"`
    ///
    /// A bare `panic;` aborts immediately. `panic(expr);` evaluates `expr` for its
    /// side effects (the value is discarded) before aborting.
    fn parse_panic(&mut self) -> Result<Stmt, String> {
        self.expect(&Tok::Panic, "to start a panic")?;
        // An optional parenthesized argument, evaluated for side effects.
        let arg = if self.eat(&Tok::LParen) {
            // Inside parentheses the `{` ambiguity is gone; allow struct literals.
            let e = self.with_struct_lit(|p| p.parse_expr())?;
            self.expect(&Tok::RParen, "after panic argument")?;
            Some(e)
        } else {
            None
        };
        self.expect(&Tok::Semi, "after panic")?;
        Ok(Stmt::Panic(arg))
    }

    // ---- grammar: proof-fragment expression forms --------------------------

    /// `match scrut { ("|"? pattern "=>" expr)+ }` as an **expression** (the form proofs
    /// and functional bodies use): each arm body is an expression, not a block, and arms
    /// may be separated (and optionally led) by `|`.
    fn parse_match_expr(&mut self) -> Result<Expr, String> {
        self.expect(&Tok::Match, "to start a match expression")?;
        let scrut = self.with_no_struct_lit(|p| p.parse_expr())?;
        self.expect(&Tok::LBrace, "to open match arms")?;
        let mut arms = Vec::new();
        while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
            self.eat(&Tok::Pipe); // optional leading/separating `|`
            let pat = self.parse_pattern()?;
            self.expect(&Tok::FatArrow, "after match pattern")?;
            let body = self.parse_expr()?;
            arms.push((pat, body));
            self.eat(&Tok::Comma); // arms may also be comma-separated
        }
        self.expect(&Tok::RBrace, "to close match arms")?;
        Ok(Expr::MatchExpr { scrut: Box::new(scrut), arms })
    }

    /// An optional QTT usage **grade** annotation right after a binder's `:`, before its
    /// type: `:0` (erased — never used at runtime), `:1` (linear — used exactly once),
    /// or no annotation at all (unrestricted/`ω`, the default — existing code is
    /// unaffected). A type never *starts* with a bare integer literal, so peeking a
    /// leading `0`/`1` token here is unambiguous with an actual type. When a grade is
    /// present, the type is wrapped as `__rv_grade0(T)` / `__rv_grade1(T)` — a marker
    /// application that `rv-driver`'s `unify` module and the kernel's `elab2` inferring
    /// elaborator recognise and strip off, building a graded `Π`/`λ` instead of the
    /// default unrestricted one. See `crates/rv-kernel/src/elab2.rs`'s `strip_grade`.
    fn parse_binder_grade(&mut self) -> Option<i64> {
        match self.peek() {
            Tok::Int(0) => {
                self.bump();
                Some(0)
            }
            Tok::Int(1) => {
                self.bump();
                Some(1)
            }
            _ => None,
        }
    }

    /// Wrap `ty` in the `__rv_grade0`/`__rv_grade1` marker application for `grade`, if
    /// `grade` is `Some`; otherwise return `ty` unchanged. See [`Self::parse_binder_grade`].
    fn apply_grade_marker(&mut self, grade: Option<i64>, ty: Expr) -> Expr {
        match grade {
            Some(g) => {
                let marker = self.syms.intern(if g == 0 { "__rv_grade0" } else { "__rv_grade1" });
                Expr::Apply { callee: Box::new(Expr::Var(marker)), args: vec![ty] }
            }
            None => ty,
        }
    }

    /// `fun binder+ "=>" body` — a dependent lambda. Each binder is `(name : type)`,
    /// `(name :0 type)` / `(name :1 type)` (a graded binder — see
    /// [`Self::parse_binder_grade`]), or a bare `name`.
    fn parse_fun(&mut self) -> Result<Expr, String> {
        self.eat_kw("fun");
        let mut params = Vec::new();
        while self.peek() != &Tok::FatArrow {
            if self.eat(&Tok::LParen) {
                let name = self.ident("as a fun parameter")?;
                let ty = if self.eat(&Tok::Colon) {
                    let grade = self.parse_binder_grade();
                    let t = self.parse_type()?;
                    let e = self.ty_to_expr(t)?;
                    Some(Box::new(self.apply_grade_marker(grade, e)))
                } else {
                    None
                };
                self.expect(&Tok::RParen, "after a fun parameter")?;
                params.push((name, ty));
            } else if matches!(self.peek(), Tok::Ident(_)) {
                let name = self.ident("as a fun parameter")?;
                params.push((name, None));
            } else {
                break;
            }
        }
        self.expect(&Tok::FatArrow, "after fun parameters")?;
        let body = self.parse_expr()?;
        Ok(Expr::Fun { params, body: Box::new(body) })
    }

    /// `forall binder+ "," body` — a dependent function *type*. Each binder is
    /// `(name : type)` or `(name :0/:1 type)` (a graded binder — see
    /// [`Self::parse_binder_grade`]).
    fn parse_forall(&mut self) -> Result<Expr, String> {
        self.eat_kw("forall");
        let mut params = Vec::new();
        while self.peek() != &Tok::Comma {
            self.expect(&Tok::LParen, "to open a forall binder")?;
            let name = self.ident("as a forall binder")?;
            self.expect(&Tok::Colon, "after a forall binder name")?;
            let grade = self.parse_binder_grade();
            let t = self.parse_type()?;
            self.expect(&Tok::RParen, "after a forall binder")?;
            let e = self.ty_to_expr(t)?;
            params.push((name, Box::new(self.apply_grade_marker(grade, e))));
        }
        self.expect(&Tok::Comma, "after forall binders")?;
        let body = self.parse_expr()?;
        Ok(Expr::Forall { params, body: Box::new(body) })
    }

    // ---- grammar: expressions (precedence climbing) ------------------------

    /// Entry point for expressions.
    fn parse_expr(&mut self) -> Result<Expr, String> {
        self.parse_bin(0)
    }

    /// Precedence-climbing core. `min_bp` is the minimum binding power this call
    /// will accept; binary operators with lower power stop the climb.
    fn parse_bin(&mut self, min_bp: u8) -> Result<Expr, String> {
        let mut lhs = self.parse_unary()?;
        loop {
            let (op, bp) = match binop_of(self.peek()) {
                Some(pair) => pair,
                None => break,
            };
            if bp < min_bp {
                break;
            }
            self.bump();
            // All our binary operators are left-associative, so the right-hand
            // side parses with strictly greater binding power.
            let rhs = self.parse_bin(bp + 1)?;
            lhs = Expr::Bin(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    /// `unary := ("-" | "!" | "*" | "&" "mut"?) unary | primary`
    ///
    /// `&`/`&mut` form borrows and `*` forms a dereference; all bind like the
    /// other prefix unary operators (tighter than any binary operator).
    fn parse_unary(&mut self) -> Result<Expr, String> {
        match self.peek() {
            Tok::Minus => {
                self.bump();
                Ok(Expr::Un(UnOp::Neg, Box::new(self.parse_unary()?)))
            }
            Tok::Bang => {
                self.bump();
                Ok(Expr::Un(UnOp::Not, Box::new(self.parse_unary()?)))
            }
            // Dereference `*expr`.
            Tok::Star => {
                self.bump();
                Ok(Expr::Deref(Box::new(self.parse_unary()?)))
            }
            // Borrow `&expr` (shared) or `&mut expr` (mutable).
            Tok::Amp => {
                self.bump();
                let mutable = self.eat_mut();
                Ok(Expr::Ref { mutable, expr: Box::new(self.parse_unary()?) })
            }
            _ => self.parse_postfix(),
        }
    }

    /// `postfix := primary ( "." IDENT ( "(" args? ")" )? | "?" )*`
    ///
    /// A `.IDENT` followed by `(` is a method call (`recv.m(args)`); otherwise it
    /// is a field access. A trailing `?` is the error-propagation operator. All are
    /// left-associative postfix forms, so chains compose (e.g. `f()?.x`).
    fn parse_postfix(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_primary()?;
        loop {
            if self.eat(&Tok::Dot) {
                let name = self.ident("as field or method name after `.`")?;
                if self.eat(&Tok::LParen) {
                    // Method call `recv.method(args)`.
                    let args = self.parse_args()?;
                    self.expect(&Tok::RParen, "after method-call arguments")?;
                    e = Expr::MethodCall { recv: Box::new(e), method: name, args };
                } else {
                    e = Expr::Field { base: Box::new(e), field: name };
                }
            } else if self.peek() == &Tok::LParen {
                // General application `callee(args)` (proof fragment, higher-order:
                // `lookup(k)(rest)`). The first-order `IDENT(args)` form is handled in
                // `parse_primary`; this picks up any *further* application of a
                // non-identifier callee.
                self.bump();
                let args = self.parse_args()?;
                self.expect(&Tok::RParen, "after application arguments")?;
                e = Expr::Apply { callee: Box::new(e), args };
            } else if self.peek() == &Tok::Lt && matches!(e, Expr::Var(_) | Expr::EnumCtor { .. }) {
                // A type-application `Name<T, …>` used as a *value* in the proof fragment
                // (e.g. `Eq::refl(Option<A>, …)`). Disambiguated from the `<` comparison
                // operator by speculative parse: a clean `< type,… >` is a type application;
                // anything else restores and lets `<` parse as comparison.
                let save = self.pos;
                match self.try_turbofish() {
                    Some(args) => e = Expr::Apply { callee: Box::new(e), args },
                    None => {
                        self.pos = save;
                        break;
                    }
                }
            } else if self.eat(&Tok::Question) {
                // Error-propagation postfix operator `expr?`.
                e = Expr::Try(Box::new(e));
            } else {
                break;
            }
        }
        Ok(e)
    }

    /// Speculatively parse a turbofish-free generic argument list `< type (, type)* >` used
    /// as a *value* (proof fragment). Returns the arguments as expressions, or `None` if the
    /// tokens are not a clean generic list (the caller then treats `<` as comparison).
    fn try_turbofish(&mut self) -> Option<Vec<Expr>> {
        if !self.eat(&Tok::Lt) {
            return None;
        }
        let mut args = Vec::new();
        loop {
            let ty = self.parse_type().ok()?;
            args.push(self.ty_to_expr(ty).ok()?);
            if self.eat(&Tok::Comma) {
                continue;
            }
            break;
        }
        if self.eat(&Tok::Gt) {
            Some(args)
        } else {
            None
        }
    }

    /// `primary := INT | "true" | "false" | "()" | IDENT | IDENT "(" args? ")" | "(" expr ")"`
    /// plus the proof-fragment atoms (`match` as an expression, `fun`, `forall`, `Type`,
    /// `Prop`, `_`, `rewrite`, `decide`, `by_cases`).
    fn parse_primary(&mut self) -> Result<Expr, String> {
        // Match as an *expression* (value-producing, `| pat => expr` arms).
        if self.peek() == &Tok::Match {
            return self.parse_match_expr();
        }
        // A let-expression in expression position (`let x := e in body`).
        if self.peek() == &Tok::Let {
            return self.parse_let_in_expr();
        }
        // Proof-fragment keyword atoms (matched by spelling).
        if self.peek_kw("fun") {
            return self.parse_fun();
        }
        if self.peek_kw("forall") {
            return self.parse_forall();
        }
        if self.peek_kw("Type") {
            self.bump();
            let n = if let Tok::Int(n) = self.peek().clone() {
                self.bump();
                n as u32
            } else {
                0
            };
            return Ok(Expr::TypeUniv(n));
        }
        if self.peek_kw("Prop") {
            self.bump();
            return Ok(Expr::Prop);
        }
        if self.peek_kw("by_decide") {
            self.bump();
            return Ok(Expr::Decide);
        }
        if self.peek_kw("rewrite") {
            self.bump();
            let eqn = self.parse_expr()?;
            self.expect(&Tok::FatArrow, "after `rewrite <eqn>`")?;
            let body = self.parse_expr()?;
            return Ok(Expr::Rewrite { eqn: Box::new(eqn), body: Box::new(body) });
        }
        if self.peek_kw("by_cases") {
            self.bump();
            let scrut = self.with_no_struct_lit(|p| p.parse_expr())?;
            self.expect(&Tok::FatArrow, "after `by_cases <scrut>`")?;
            let tbody = self.parse_expr()?;
            self.expect(&Tok::Pipe, "between `by_cases` branches")?;
            let fbody = self.parse_expr()?;
            return Ok(Expr::ByCases {
                scrut: Box::new(scrut),
                tbody: Box::new(tbody),
                fbody: Box::new(fbody),
            });
        }
        // A hole `_` (an inference variable in the proof fragment).
        if matches!(self.peek(), Tok::Ident(n) if n == "_") {
            self.bump();
            return Ok(Expr::Hole);
        }
        match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                Ok(Expr::Int(n))
            }
            Tok::Float(f) => {
                self.bump();
                Ok(Expr::Float(f))
            }
            Tok::Str(s) => {
                self.bump();
                Ok(Expr::Str(s))
            }
            // A closure literal `|x, y| body` (or `|| body`).
            Tok::Pipe => {
                self.bump();
                let mut params = Vec::new();
                if self.peek() != &Tok::Pipe {
                    loop {
                        params.push(self.ident("as a closure parameter")?);
                        // An optional `: Type` annotation is accepted and erased (closures are
                        // type-erased; the body is checked structurally).
                        if self.eat(&Tok::Colon) {
                            let _ = self.parse_type()?;
                        }
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                self.expect(&Tok::Pipe, "to close the closure parameter list")?;
                let body = Box::new(self.parse_expr()?);
                Ok(Expr::Lambda { params, body })
            }
            Tok::True => {
                self.bump();
                Ok(Expr::Bool(true))
            }
            Tok::False => {
                self.bump();
                Ok(Expr::Bool(false))
            }
            Tok::Ident(name) => {
                self.bump();
                let sym = self.syms.intern(&name);
                if self.eat(&Tok::LParen) {
                    // Function call.
                    let args = self.parse_args()?;
                    self.expect(&Tok::RParen, "after call arguments")?;
                    Ok(Expr::Call { func: sym, args })
                } else if self.eat(&Tok::ColonColon) {
                    // Enum constructor `Enum::Variant` or `Enum::Variant(args)`.
                    let variant = self.variant_name("as enum variant")?;
                    let args = if self.eat(&Tok::LParen) {
                        let a = self.parse_args()?;
                        self.expect(&Tok::RParen, "after enum constructor arguments")?;
                        a
                    } else {
                        Vec::new()
                    };
                    Ok(Expr::EnumCtor { enum_name: sym, variant, args })
                } else if !self.no_struct_lit && self.peek() == &Tok::LBrace {
                    // Struct literal `Name { f: e, ... }` — only in expression
                    // position (disabled in if/while/match conditions).
                    self.parse_struct_lit(sym)
                } else {
                    Ok(Expr::Var(sym))
                }
            }
            Tok::LParen => {
                self.bump();
                // `()` is the unit literal; otherwise a parenthesized expression.
                if self.eat(&Tok::RParen) {
                    Ok(Expr::Unit)
                } else {
                    // Inside parentheses the `{` ambiguity is gone; allow struct
                    // literals again for the inner expression.
                    let e = self.with_struct_lit(|p| p.parse_expr())?;
                    self.expect(&Tok::RParen, "to close a parenthesized expression")?;
                    Ok(e)
                }
            }
            other => Err(format!(
                "line {}: expected an expression, found {other:?}",
                self.line()
            )),
        }
    }

    /// `struct_lit := IDENT "{" ( IDENT ":" expr ("," ...)* ","? )? "}"`.
    /// The opening `IDENT` (`name`) has already been consumed.
    fn parse_struct_lit(&mut self, name: rv_core::Sym) -> Result<Expr, String> {
        self.expect(&Tok::LBrace, "to open a struct literal")?;
        let mut fields = Vec::new();
        // Field values are full expressions, so struct literals are allowed
        // again inside them (the no_struct_lit guard only covers the bare `{`).
        let prev = self.no_struct_lit;
        self.no_struct_lit = false;
        let result: Result<(), String> = (|| {
            while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
                let fname = self.ident("as struct-literal field name")?;
                self.expect(&Tok::Colon, "after struct-literal field name")?;
                let value = self.parse_expr()?;
                fields.push((fname, value));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(&Tok::RBrace, "to close a struct literal")?;
            Ok(())
        })();
        self.no_struct_lit = prev;
        result?;
        Ok(Expr::StructLit { name, fields })
    }

    /// `args := expr ("," expr)*` (possibly empty). Inside parentheses, struct
    /// literals are unambiguous, so re-enable them for argument expressions.
    fn parse_args(&mut self) -> Result<Vec<Expr>, String> {
        let mut args = Vec::new();
        if self.peek() == &Tok::RParen {
            return Ok(args);
        }
        let prev = self.no_struct_lit;
        self.no_struct_lit = false;
        let result: Result<(), String> = (|| {
            loop {
                args.push(self.parse_expr()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            Ok(())
        })();
        self.no_struct_lit = prev;
        result?;
        Ok(args)
    }
}

/// Parse the executable fixed-width integer spellings. `isize`/`usize` are
/// modeled as 64-bit values on Raven's current 64-bit VM target.
fn fixed_int_ty(name: &str) -> Option<rv_core::IntTy> {
    let (signed, bits) = match name {
        "i8" => (true, 8),
        "i16" => (true, 16),
        "i32" => (true, 32),
        "u8" => (false, 8),
        "u16" => (false, 16),
        "u32" => (false, 32),
        "u64" | "usize" => (false, 64),
        "isize" => (true, 64),
        // 128-bit spellings. Their *type* (range/overflow reasoning) is modeled
        // exactly by the verifier's width machinery ([`rv_core::IntTy`] bounds); on
        // the current 64-bit VM their runtime values are modeled at the 64-bit
        // machine word, as `isize`/`usize` are.
        "i128" => (true, 128),
        "u128" => (false, 128),
        _ => return None,
    };
    Some(rv_core::IntTy { signed, bits })
}

/// Map a token to its binary operator and binding power (higher binds tighter).
/// Mirrors the grammar's precedence ladder (lowest -> highest):
/// `||` < `&&` < `== !=` < `< <= > >=` < `+ -` < `* / %`.
fn binop_of(tok: &Tok) -> Option<(BinOp, u8)> {
    Some(match tok {
        Tok::OrOr => (BinOp::Or, 1),
        Tok::AndAnd => (BinOp::And, 2),
        Tok::EqEq => (BinOp::Eq, 3),
        Tok::NotEq => (BinOp::Ne, 3),
        Tok::Lt => (BinOp::Lt, 4),
        Tok::Le => (BinOp::Le, 4),
        Tok::Gt => (BinOp::Gt, 4),
        Tok::Ge => (BinOp::Ge, 4),
        Tok::Plus => (BinOp::Add, 5),
        Tok::Minus => (BinOp::Sub, 5),
        Tok::Star => (BinOp::Mul, 6),
        Tok::Slash => (BinOp::Div, 6),
        Tok::Percent => (BinOp::Mod, 6),
        _ => return None,
    })
}

/// Human-readable description of an expected token for error messages.
fn describe(tok: &Tok) -> String {
    match tok {
        Tok::LParen => "`(`".into(),
        Tok::RParen => "`)`".into(),
        Tok::LBrace => "`{`".into(),
        Tok::RBrace => "`}`".into(),
        Tok::Comma => "`,`".into(),
        Tok::Colon => "`:`".into(),
        Tok::ColonColon => "`::`".into(),
        Tok::Semi => "`;`".into(),
        Tok::Dot => "`.`".into(),
        Tok::Arrow => "`->`".into(),
        Tok::FatArrow => "`=>`".into(),
        Tok::Eq => "`=`".into(),
        Tok::Question => "`?`".into(),
        Tok::Fn => "`fn`".into(),
        other => format!("{other:?}"),
    }
}
