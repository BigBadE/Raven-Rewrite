//! `#[requires(..)]` / `#[ensures(..)]` specs from function attributes.
//!
//! The attribute argument is an opaque token tree; we take its text and re-parse
//! it as a Rust expression (with `ra_ap_syntax`), then lower it to a first-order
//! `Prop`. Spec expressions are pure scalars (literals, variables, comparisons,
//! `&&`/`||`/`!`, arithmetic); `result` denotes the return value in `ensures`.

use ra_ap_syntax::ast::{self, HasAttrs};
use ra_ap_syntax::{AstNode, Edition, SourceFile};

use rv_core::{BinOp, Prop, Symbols, Term, UnOp};

/// Collect a function's pre/post conditions (`Prop::True` if absent).
pub fn collect(f: &ast::Fn, syms: &mut Symbols) -> Result<(Prop, Prop), String> {
    let mut pre = Prop::True;
    let mut post = Prop::True;
    for attr in f.attrs() {
        let Some(meta) = attr.meta() else { continue };
        let Some(path) = meta.path() else { continue };
        let name = path.syntax().text().to_string();
        let is_pre = name.trim() == "requires";
        let is_post = name.trim() == "ensures";
        if !is_pre && !is_post {
            continue;
        }
        let tt = meta
            .syntax()
            .children()
            .find_map(ast::TokenTree::cast)
            .ok_or_else(|| format!("`#[{name}(..)]` needs a parenthesised expression"))?;
        let inner = strip_parens(&tt.syntax().text().to_string());
        let prop = parse_prop(&inner, syms).map_err(|e| format!("in `#[{name}(..)]`: {e}"))?;
        if is_pre {
            pre = pre.and(prop);
        } else {
            post = post.and(prop);
        }
    }
    Ok((pre, post))
}

/// Publicly re-usable: parse a standalone boolean expression (e.g. an `assert!`
/// condition) into a `Prop`.
pub fn parse_prop(expr_src: &str, syms: &mut Symbols) -> Result<Prop, String> {
    let wrapped = format!("fn __spec() {{ {expr_src} }}");
    let parse = SourceFile::parse(&wrapped, Edition::Edition2021);
    if let Some(err) = parse.errors().first() {
        return Err(format!("could not parse spec expression `{expr_src}`: {err}"));
    }
    let file = parse.tree();
    let f = file
        .syntax()
        .descendants()
        .find_map(ast::Fn::cast)
        .ok_or("empty spec")?;
    let expr = f
        .body()
        .and_then(|b| b.stmt_list())
        .and_then(|l| l.tail_expr())
        .ok_or("empty spec expression")?;
    lower_prop(&expr, syms)
}

fn strip_parens(s: &str) -> String {
    let s = s.trim();
    s.strip_prefix('(').and_then(|s| s.strip_suffix(')')).unwrap_or(s).trim().to_string()
}

fn lower_prop(e: &ast::Expr, syms: &mut Symbols) -> Result<Prop, String> {
    match e {
        ast::Expr::ParenExpr(p) => lower_prop(&p.expr().ok_or("empty `()`")?, syms),
        ast::Expr::Literal(lit) => match lit.kind() {
            ast::LiteralKind::Bool(true) => Ok(Prop::True),
            ast::LiteralKind::Bool(false) => Ok(Prop::False),
            _ => Ok(Prop::Holds(lower_term(e, syms)?)),
        },
        ast::Expr::PrefixExpr(p) if matches!(p.op_kind(), Some(ast::UnaryOp::Not)) => {
            Ok(lower_prop(&p.expr().ok_or("missing `!` operand")?, syms)?.not())
        }
        ast::Expr::BinExpr(b) => match b.op_kind() {
            Some(ast::BinaryOp::LogicOp(ast::LogicOp::And)) => {
                Ok(lower_prop(&b.lhs().ok_or("missing lhs")?, syms)?
                    .and(lower_prop(&b.rhs().ok_or("missing rhs")?, syms)?))
            }
            Some(ast::BinaryOp::LogicOp(ast::LogicOp::Or)) => {
                Ok(lower_prop(&b.lhs().ok_or("missing lhs")?, syms)?
                    .or(lower_prop(&b.rhs().ok_or("missing rhs")?, syms)?))
            }
            _ => Ok(Prop::Holds(lower_term(e, syms)?)),
        },
        _ => Ok(Prop::Holds(lower_term(e, syms)?)),
    }
}

fn lower_term(e: &ast::Expr, syms: &mut Symbols) -> Result<Term, String> {
    match e {
        ast::Expr::ParenExpr(p) => lower_term(&p.expr().ok_or("empty `()`")?, syms),
        ast::Expr::Literal(lit) => match lit.kind() {
            ast::LiteralKind::IntNumber(n) => {
                Ok(Term::Int(n.value().map_err(|_| "bad integer literal")? as i64))
            }
            ast::LiteralKind::Bool(b) => Ok(Term::Bool(b)),
            _ => Err("unsupported literal in spec".to_string()),
        },
        ast::Expr::PathExpr(pe) => {
            let path = pe.path().ok_or("empty path")?;
            if path.qualifier().is_some() {
                return Err("qualified path not allowed in spec".to_string());
            }
            let name = path.segment().and_then(|s| s.name_ref()).ok_or("path without name")?.text().to_string();
            Ok(Term::Var(syms.intern(&name)))
        }
        ast::Expr::PrefixExpr(p) => {
            let inner = lower_term(&p.expr().ok_or("missing operand")?, syms)?;
            match p.op_kind() {
                Some(ast::UnaryOp::Neg) => Ok(Term::un(UnOp::Neg, inner)),
                Some(ast::UnaryOp::Not) => Ok(Term::un(UnOp::Not, inner)),
                _ => Err("unsupported unary operator in spec".to_string()),
            }
        }
        ast::Expr::BinExpr(b) => {
            let op = spec_bin_op(b).ok_or("unsupported operator in spec")?;
            let a = lower_term(&b.lhs().ok_or("missing lhs")?, syms)?;
            let c = lower_term(&b.rhs().ok_or("missing rhs")?, syms)?;
            Ok(Term::bin(op, a, c))
        }
        other => Err(format!("`{:?}` is not allowed in a specification", other.syntax().kind())),
    }
}

fn spec_bin_op(b: &ast::BinExpr) -> Option<BinOp> {
    match b.op_kind()? {
        ast::BinaryOp::ArithOp(ast::ArithOp::Add) => Some(BinOp::Add),
        ast::BinaryOp::ArithOp(ast::ArithOp::Sub) => Some(BinOp::Sub),
        ast::BinaryOp::ArithOp(ast::ArithOp::Mul) => Some(BinOp::Mul),
        ast::BinaryOp::ArithOp(ast::ArithOp::Div) => Some(BinOp::Div),
        ast::BinaryOp::ArithOp(ast::ArithOp::Rem) => Some(BinOp::Mod),
        ast::BinaryOp::LogicOp(ast::LogicOp::And) => Some(BinOp::And),
        ast::BinaryOp::LogicOp(ast::LogicOp::Or) => Some(BinOp::Or),
        ast::BinaryOp::CmpOp(ast::CmpOp::Eq { negated }) => Some(if negated { BinOp::Ne } else { BinOp::Eq }),
        ast::BinaryOp::CmpOp(ast::CmpOp::Ord { ordering, strict }) => Some(match (ordering, strict) {
            (ast::Ordering::Less, true) => BinOp::Lt,
            (ast::Ordering::Less, false) => BinOp::Le,
            (ast::Ordering::Greater, true) => BinOp::Gt,
            (ast::Ordering::Greater, false) => BinOp::Ge,
        }),
        _ => None,
    }
}
