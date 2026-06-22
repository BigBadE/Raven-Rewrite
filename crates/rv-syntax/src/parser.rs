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

    /// `program := (fn_decl | struct_decl | enum_decl | trait_decl | impl_decl)*`
    pub fn parse_module(&mut self) -> Result<Module, String> {
        let mut items = Vec::new();
        while self.peek() != &Tok::Eof {
            match self.peek() {
                Tok::Fn => items.push(Item::Fn(self.parse_fn()?)),
                Tok::Struct => items.push(Item::Struct(self.parse_struct()?)),
                Tok::Enum => items.push(Item::Enum(self.parse_enum()?)),
                Tok::Trait => items.push(Item::Trait(self.parse_trait()?)),
                Tok::Impl => items.push(Item::Impl(self.parse_impl()?)),
                other => {
                    return Err(format!(
                        "line {}: expected an item (`fn`, `struct`, `enum`, `trait`, or `impl`), \
                         found {other:?}",
                        self.line()
                    ))
                }
            }
        }
        Ok(Module { items })
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

    /// `enum_decl := "enum" IDENT "{" ( variant ("," ...)* ","? )? "}"`
    /// `variant   := IDENT ( "(" type ("," type)* ")" )?`
    fn parse_enum(&mut self) -> Result<EnumDecl, String> {
        self.expect(&Tok::Enum, "to start an enum")?;
        let name = self.ident("as enum name")?;
        let generics = self.parse_generics()?;
        self.expect(&Tok::LBrace, "to open enum variants")?;
        let mut variants = Vec::new();
        while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
            let vname = self.ident("as variant name")?;
            let mut field_tys = Vec::new();
            if self.eat(&Tok::LParen) {
                loop {
                    field_tys.push(self.parse_type()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(&Tok::RParen, "after variant field types")?;
            }
            variants.push(VariantDecl { name: vname, fields: field_tys });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(&Tok::RBrace, "to close enum variants")?;
        Ok(EnumDecl { name, generics, variants })
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
            params.push(Param { name, ty });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        Ok(params)
    }

    /// `type := "&" "mut"? type | "i64" | "bool" | "()" | IDENT`
    /// (an `IDENT` is a named ADT; a leading `&`/`&mut` forms a reference type).
    fn parse_type(&mut self) -> Result<Ty, String> {
        // Reference type: `&T` or `&mut T`. `mut` arrives from the lexer as an
        // ordinary identifier, so we test its spelling rather than a keyword token.
        if self.eat(&Tok::Amp) {
            let mutable = self.eat_mut();
            let inner = self.parse_type()?;
            return Ok(Ty::Ref { mutable, inner: Box::new(inner) });
        }
        match self.peek().clone() {
            // `i64` and `bool` arrive as identifiers from the lexer.
            Tok::Ident(name) if name == "i64" => {
                self.bump();
                Ok(Ty::I64)
            }
            Tok::Ident(name) if name == "bool" => {
                self.bump();
                Ok(Ty::Bool)
            }
            // Any other identifier names a user-defined struct/enum, an optional
            // generic application (`Base<arg, ...>`), or — resolved at lowering —
            // a bare type parameter.
            Tok::Ident(name) => {
                self.bump();
                let base = self.syms.intern(&name);
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
                    Ok(Ty::Generic { base, args })
                } else {
                    Ok(Ty::Adt(base))
                }
            }
            Tok::LParen => {
                self.bump();
                self.expect(&Tok::RParen, "to complete the unit type `()`")?;
                Ok(Ty::Unit)
            }
            other => Err(format!(
                "line {}: expected a type (`i64`, `bool`, `()`, or a type name), found {other:?}",
                self.line()
            )),
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
                self.expect(&Tok::Semi, "after expression statement")?;
                Ok(Stmt::Expr(e))
            }
        }
    }

    /// Lookahead: is the current `IDENT` immediately followed by a `=` (and not
    /// `==`)? Used to disambiguate assignment from an expression statement.
    fn peek_is_assignment(&self) -> bool {
        matches!(self.peek(), Tok::Ident(_))
            && self.pos + 1 < self.toks.len()
            && self.toks[self.pos + 1].tok == Tok::Eq
    }

    /// `"let" IDENT (":" type)? "=" expr ";"`
    fn parse_let(&mut self) -> Result<Stmt, String> {
        self.expect(&Tok::Let, "to start a let binding")?;
        let name = self.ident("as let binding name")?;
        let ty = if self.eat(&Tok::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };
        self.expect(&Tok::Eq, "in let binding")?;
        let init = self.parse_expr()?;
        self.expect(&Tok::Semi, "after let binding")?;
        Ok(Stmt::Let { name, ty, init })
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
        let variant = self.ident("as variant name in pattern")?;
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
            } else if self.eat(&Tok::Question) {
                // Error-propagation postfix operator `expr?`.
                e = Expr::Try(Box::new(e));
            } else {
                break;
            }
        }
        Ok(e)
    }

    /// `primary := INT | "true" | "false" | "()" | IDENT | IDENT "(" args? ")" | "(" expr ")"`
    fn parse_primary(&mut self) -> Result<Expr, String> {
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
                    let variant = self.ident("as enum variant")?;
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
