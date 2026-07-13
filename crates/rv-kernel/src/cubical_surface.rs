//! Surfacing `rv_kernel_core`'s cubical layer (`Path`/`PathP`, `PLam`/`PApp`, the
//! interval, and the derived operators `refl`/`ap`/`transport`/`subst`/`J`/`trans`/
//! `path_to_eq`/`eq_to_path`) as ordinary, by-name-callable `.rv` constants.
//!
//! ## Why definitions, not new surface grammar
//!
//! The cubical layer's building blocks (`Term::I`/`IZero`/`IOne`/`INeg`/`IMeet`/
//! `IJoin`, `Term::PLam`/`PApp`/`PathP`, and the derived combinators in
//! [`rv_kernel_core::cubical`]) are *terms*, not new binder forms the parser needs to
//! know about. Every one of them can be packaged as an ordinary, fully-explicit
//! **function** — `Path`, `PathP`, `plam`, `papp`, `i0`, `i1`, `ineg`, `imeet`,
//! `ijoin`, `refl`, `ap`, `pfunext`, `transport`, `subst`, `J`, `trans`, `path_to_eq`,
//! `eq_to_path` — installed once as [`rv_kernel_core::env::Decl::Def`] constants
//! (exactly like [`crate::funext::install_funext`]) and then referenced from `.rv`
//! source through the ordinary `Expr::Var`/`Expr::Call` path — no grammar change
//! needed in `rv-syntax` at all. This mirrors how `Quot`/`Trunc`'s constants are
//! already surfaced (installed once, then just names).
//!
//! Each constant's declared TYPE is checked well-formed, and its VALUE is
//! type-checked against that type, by the ordinary [`rv_kernel_core::check::Checker`]
//! at install time — nothing here is trusted beyond what `add_definition`/
//! `install_funext` already are: a bug in this module can only make installation
//! *fail*, never make an unsound term verify (the kernel re-checks everything).
//!
//! `plam`'s calling convention makes it usable from `.rv` without any interval-binder
//! syntax: it takes an ordinary function `f : Π (i:I). A i` (written as a ordinary
//! `fun i => …` in the proof fragment, since `I` is just another type) and produces
//! `PathP A (f i0) (f i1)`; `papp p r` eliminates it. `Path A a b` is the
//! non-dependent special case (`PathP` with a constant family).

use rv_kernel_core::check::{Checker, LocalCtx};
use rv_kernel_core::cubical;
use rv_kernel_core::env::{Decl, Env};
use rv_kernel_core::level::Level;
use rv_kernel_core::term::{name, Term};

/// A tiny named-variable context for building deep terms by name instead of by
/// hand-counted de Bruijn indices — identical in spirit to [`crate::funext`]'s
/// private `Ctx` helper, duplicated here (small enough, and keeps this module
/// self-contained).
#[derive(Clone)]
struct Ctx(Vec<&'static str>);
impl Ctx {
    fn v(&self, n: &str) -> Term {
        let pos = self.0.iter().rposition(|&x| x == n).unwrap_or_else(|| panic!("unbound '{n}'"));
        Term::Var(self.0.len() - 1 - pos)
    }
    fn push(&self, n: &'static str) -> Ctx {
        let mut v = self.0.clone();
        v.push(n);
        Ctx(v)
    }
}
fn lam(ctx: &Ctx, dom: Term, n: &'static str, f: impl FnOnce(&Ctx) -> Term) -> Term {
    Term::lam(dom, f(&ctx.push(n)))
}
fn pi(ctx: &Ctx, dom: Term, n: &'static str, f: impl FnOnce(&Ctx) -> Term) -> Term {
    Term::pi(dom, f(&ctx.push(n)))
}

/// `Eq.{lvl} T x y`.
fn eq_app(lvl: Level, t: Term, x: Term, y: Term) -> Term {
    Term::apps(Term::cnst(name("Eq"), vec![lvl]), [t, x, y])
}

/// Install one constant, type-checking its value against its type first.
fn install(env: &mut Env, n: &str, num_levels: u32, ty: Term, value: Term) -> Result<(), String> {
    if env.contains(n) {
        return Err(format!("'{n}' is already declared"));
    }
    {
        let chk = Checker::new(env);
        chk.infer_sort(&mut LocalCtx::new(), &ty).map_err(|e| format!("{n}: type is not well-formed: {e}"))?;
        chk.check(&mut LocalCtx::new(), &value, &ty).map_err(|e| format!("{n}: value does not match type: {e}"))?;
    }
    env.insert(name(n), Decl::Def { num_levels, ty, value })
}

/// Install the whole surfaced cubical layer: `i0`/`i1`/`ineg`/`imeet`/`ijoin`, `Path`/
/// `PathP`/`plam`/`papp`, and the derived operators `refl`/`ap`/`pfunext`/
/// `transport`/`subst`/`J`/`trans`/`path_to_eq`/`eq_to_path`. Requires `Eq` (the
/// inductive equality) to already be declared — only `path_to_eq`/`eq_to_path` need
/// it, but it is required up front for a single, simple precondition.
pub fn install_cubical(env: &mut Env) -> Result<(), String> {
    if !env.contains("Eq") {
        return Err("the surfaced cubical layer requires 'Eq' to already be declared".to_string());
    }

    let root = Ctx(vec![]);

    // NOTE: `i0`/`i1`/`ineg`/`imeet`/`ijoin`/`Path`/`PathP`/`plam`/`papp` are **not**
    // installed here as ordinary `Decl::Def` constants: `I` (the interval) is
    // deliberately *not* a fibrant type (see `rv_kernel_core::check::Checker::infer`'s
    // `Term::I` arm — `infer_sort(I)` errors on purpose, so `I` can never be an
    // ordinary `Π`-domain). Those forms are instead genuine surface syntax, handled
    // directly by [`crate::elab2::Infer`] (see `crate::surface::Expr::{IZero,IOne,
    // INeg,IMeet,IJoin,PLam,PApp,PathTy,PathPTy}`), which manipulates the interval the
    // same way `Checker` itself does — via `LocalCtx`, never via `Term::Pi`.

    // ---- Path.{u} : Pi (A:Sort u) (a b:A). Sort u ------------------------------
    {
        let u = Level::param(0);
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, c1.v("A"), "a", |c2| pi(c2, c2.v("A"), "b", |_| Term::Sort(u.clone())))
        });
        let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
            lam(c1, c1.v("A"), "a", |c2| lam(c2, c2.v("A"), "b", |c3| Term::path(c3.v("A"), c3.v("a"), c3.v("b"))))
        });
        install(env, "Path", 1, ty, value)?;
    }

    // ---- refl.{u} : Pi (A:Sort u)(a:A). Path A a a -----------------------------
    {
        let u = Level::param(0);
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, c1.v("A"), "a", |c2| Term::path(c2.v("A"), c2.v("a"), c2.v("a")))
        });
        let value = lam(&root, Term::Sort(u), "A", |c1| lam(c1, c1.v("A"), "a", |c2| cubical::refl(&c2.v("a"))));
        install(env, "refl", 1, ty, value)?;
    }

    // ---- ap.{u,v} : Pi (A:Sort u)(B:Sort v)(a b:A)(f:A->B)(p: Path A a b).
    //                    Path B (f a) (f b) --------------------------------------
    {
        let u = Level::param(0);
        let v = Level::param(1);
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, Term::Sort(v.clone()), "B", |c2| {
                pi(c2, c2.v("A"), "a", |c3| {
                    pi(c3, c3.v("A"), "b", |c4| {
                        let ab = Term::arrow(c4.v("A"), c4.v("B"));
                        pi(c4, ab, "f", |c5| {
                            let path_ab = Term::path(c5.v("A"), c5.v("a"), c5.v("b"));
                            pi(c5, path_ab, "p", |c6| {
                                Term::path(c6.v("B"), Term::app(c6.v("f"), c6.v("a")), Term::app(c6.v("f"), c6.v("b")))
                            })
                        })
                    })
                })
            })
        });
        let value = lam(&root, Term::Sort(u), "A", |c1| {
            lam(c1, Term::Sort(v), "B", |c2| {
                lam(c2, c2.v("A"), "a", |c3| {
                    lam(c3, c3.v("A"), "b", |c4| {
                        let ab = Term::arrow(c4.v("A"), c4.v("B"));
                        lam(c4, ab, "f", |c5| {
                            let path_ab = Term::path(c5.v("A"), c5.v("a"), c5.v("b"));
                            lam(c5, path_ab, "p", |c6| cubical::ap(&c6.v("f"), &c6.v("p")))
                        })
                    })
                })
            })
        });
        install(env, "ap", 2, ty, value)?;
    }

    // ---- pfunext.{u,v} : dependent function extensionality, direct cubical proof --
    // Pi (A:Sort u)(B:A->Sort v)(f g: Pi x:A. B x)
    //    (h: Pi x:A. Path (B x) (f x) (g x)). Path (Pi x:A. B x) f g
    {
        let u = Level::param(0);
        let v = Level::param(1);
        // `pix(c) := Pi (x:A). B x`, rebuilt fresh at whichever context `c` is passed
        // (rather than cloning one precomputed term and hand-lifting it past a varying
        // number of intervening binders — `Ctx::v`'s by-name lookup makes this the
        // less error-prone way to reuse a subterm across several different depths).
        let pix = |c: &Ctx| pi(c, c.v("A"), "x", |c2| Term::app(c2.v("B"), c2.v("x")));
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            let bty = Term::arrow(c1.v("A"), Term::Sort(v.clone()));
            pi(c1, bty, "B", |c2| {
                let ft = pix(c2);
                pi(c2, ft, "f", |c3| {
                    let gt = pix(c3);
                    pi(c3, gt, "g", |c4| {
                        let hty = pi(c4, c4.v("A"), "x", |c5| {
                            Term::path(
                                Term::app(c5.v("B"), c5.v("x")),
                                Term::app(c5.v("f"), c5.v("x")),
                                Term::app(c5.v("g"), c5.v("x")),
                            )
                        });
                        pi(c4, hty, "h", |c5| Term::path(pix(c5), c5.v("f"), c5.v("g")))
                    })
                })
            })
        });
        let value = lam(&root, Term::Sort(u), "A", |c1| {
            let bty = Term::arrow(c1.v("A"), Term::Sort(v));
            lam(c1, bty, "B", |c2| {
                let ft = pix(c2);
                lam(c2, ft, "f", |c3| {
                    let gt = pix(c3);
                    lam(c3, gt, "g", |c4| {
                        let hty = pi(c4, c4.v("A"), "x", |c5| {
                            Term::path(
                                Term::app(c5.v("B"), c5.v("x")),
                                Term::app(c5.v("f"), c5.v("x")),
                                Term::app(c5.v("g"), c5.v("x")),
                            )
                        });
                        lam(c4, hty, "h", |c5| cubical::funext(&c5.v("A"), &c5.v("h")))
                    })
                })
            })
        });
        install(env, "pfunext", 2, ty, value)?;
    }

    // ---- transport.{u} : Pi (A B:Sort u)(p:Path (Sort u) A B)(a:A). B ----------
    {
        let u = Level::param(0);
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, Term::Sort(u.clone()), "B", |c2| {
                let path_ty = Term::path(Term::Sort(u.clone()), c2.v("A"), c2.v("B"));
                pi(c2, path_ty, "p", |c3| pi(c3, c3.v("A"), "a", |c4| c4.v("B")))
            })
        });
        let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
            lam(c1, Term::Sort(u.clone()), "B", |c2| {
                let path_ty = Term::path(Term::Sort(u.clone()), c2.v("A"), c2.v("B"));
                lam(c2, path_ty, "p", |c3| lam(c3, c3.v("A"), "a", |c4| cubical::transport(&c4.v("p"), &c4.v("a"))))
            })
        });
        install(env, "transport", 1, ty, value)?;
    }

    // ---- psubst.{u,v} : Pi (A:Sort u)(P:A->Sort v)(a b:A)(p:Path A a b)(pa: P a). P b
    {
        let u = Level::param(0);
        let v = Level::param(1);
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            let pty = Term::arrow(c1.v("A"), Term::Sort(v.clone()));
            pi(c1, pty, "P", |c2| {
                pi(c2, c2.v("A"), "a", |c3| {
                    pi(c3, c3.v("A"), "b", |c4| {
                        let path_ab = Term::path(c4.v("A"), c4.v("a"), c4.v("b"));
                        pi(c4, path_ab, "p", |c5| {
                            let pa = Term::app(c5.v("P"), c5.v("a"));
                            pi(c5, pa, "pa", |c6| Term::app(c6.v("P"), c6.v("b")))
                        })
                    })
                })
            })
        });
        let value = lam(&root, Term::Sort(u), "A", |c1| {
            let pty = Term::arrow(c1.v("A"), Term::Sort(v));
            lam(c1, pty, "P", |c2| {
                lam(c2, c2.v("A"), "a", |c3| {
                    lam(c3, c3.v("A"), "b", |c4| {
                        let path_ab = Term::path(c4.v("A"), c4.v("a"), c4.v("b"));
                        lam(c4, path_ab, "p", |c5| {
                            let pa = Term::app(c5.v("P"), c5.v("a"));
                            lam(c5, pa, "pa", |c6| cubical::subst(&c6.v("P"), &c6.v("p"), &c6.v("pa")))
                        })
                    })
                })
            })
        });
        install(env, "psubst", 2, ty, value)?;
    }

    // ---- J.{u,v} : Pi (A:Sort u)(a:A)(C: Pi(x:A). Path A a x -> Sort v)
    //                   (d: C a (refl a))(x:A)(p: Path A a x). C x p ------------
    {
        let u = Level::param(0);
        let v = Level::param(1);
        let cty = |c: &Ctx| {
            pi(c, c.v("A"), "x", |c2| {
                let path_ax = Term::path(c2.v("A"), c2.v("a"), c2.v("x"));
                Term::arrow(path_ax, Term::Sort(v.clone()))
            })
        };
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, c1.v("A"), "a", |c2| {
                let ct = cty(c2);
                pi(c2, ct, "C", |c3| {
                    let refl_a = cubical::refl(&c3.v("a"));
                    let d_ty = Term::apps(c3.v("C"), [c3.v("a"), refl_a]);
                    pi(c3, d_ty, "d", |c4| {
                        pi(c4, c4.v("A"), "x", |c5| {
                            let path_ax = Term::path(c5.v("A"), c5.v("a"), c5.v("x"));
                            pi(c5, path_ax, "p", |c6| {
                                Term::apps(c6.v("C"), [c6.v("x"), c6.v("p")])
                            })
                        })
                    })
                })
            })
        });
        let value = lam(&root, Term::Sort(u), "A", |c1| {
            lam(c1, c1.v("A"), "a", |c2| {
                let ct = cty(c2);
                lam(c2, ct, "C", |c3| {
                    let refl_a = cubical::refl(&c3.v("a"));
                    let d_ty = Term::apps(c3.v("C"), [c3.v("a"), refl_a]);
                    lam(c3, d_ty, "d", |c4| {
                        lam(c4, c4.v("A"), "x", |c5| {
                            let path_ax = Term::path(c5.v("A"), c5.v("a"), c5.v("x"));
                            lam(c5, path_ax, "p", |c6| cubical::j(&c6.v("C"), &c6.v("d"), &c6.v("p")))
                        })
                    })
                })
            })
        });
        install(env, "J", 2, ty, value)?;
    }

    // ---- ptrans.{u} : Pi (A:Sort u)(a b c:A)(p: Path A a b)(q: Path A b c). Path A a c
    // Derived via `J`, standard proof: eliminate `p` with motive
    // `C := \(y:A)(_:Path A a y). Path A y c -> Path A a c`, base case `d := \(q:Path A
    // a c). q`, giving `J .. p : Path A b c -> Path A a c`; apply to `q`.
    {
        let u = Level::param(0);
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, c1.v("A"), "a", |c2| {
                pi(c2, c2.v("A"), "b", |c3| {
                    pi(c3, c3.v("A"), "c", |c4| {
                        let path_ab = Term::path(c4.v("A"), c4.v("a"), c4.v("b"));
                        pi(c4, path_ab, "p", |c5| {
                            let path_bc = Term::path(c5.v("A"), c5.v("b"), c5.v("c"));
                            pi(c5, path_bc, "q", |c6| Term::path(c6.v("A"), c6.v("a"), c6.v("c")))
                        })
                    })
                })
            })
        });
        let value = lam(&root, Term::Sort(u), "A", |c1| {
            lam(c1, c1.v("A"), "a", |c2| {
                lam(c2, c2.v("A"), "b", |c3| {
                    lam(c3, c3.v("A"), "c", |c4| {
                        let path_ab = Term::path(c4.v("A"), c4.v("a"), c4.v("b"));
                        lam(c4, path_ab, "p", |c5| {
                            let path_bc = Term::path(c5.v("A"), c5.v("b"), c5.v("c"));
                            lam(c5, path_bc, "q", |c6| {
                                // motive := \(y:A)(_:Path A a y). Path A y c -> Path A a c
                                let a = c6.v("a");
                                let cc = c6.v("c");
                                let motive = lam(c6, c6.v("A"), "y", |m1| {
                                    let path_ay = Term::path(m1.v("A"), a.clone().lift(1, 0), m1.v("y"));
                                    lam(m1, path_ay, "_h", |m2| {
                                        Term::arrow(
                                            Term::path(m2.v("A"), m2.v("y"), cc.clone().lift(2, 0)),
                                            Term::path(m2.v("A"), a.clone().lift(2, 0), cc.clone().lift(2, 0)),
                                        )
                                    })
                                });
                                // d : Path A a c -> Path A a c, the identity.
                                let d = lam(c6, Term::path(c6.v("A"), c6.v("a"), c6.v("c")), "z", |z| z.v("z"));
                                Term::app(cubical::j(&motive, &d, &c6.v("p")), c6.v("q"))
                            })
                        })
                    })
                })
            })
        });
        install(env, "ptrans", 1, ty, value)?;
    }

    // ---- path_to_eq.{u} : Pi (A:Sort u)(a b:A)(p:Path A a b). Eq A a b ---------
    {
        let u = Level::param(0);
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, c1.v("A"), "a", |c2| {
                pi(c2, c2.v("A"), "b", |c3| {
                    let path_ab = Term::path(c3.v("A"), c3.v("a"), c3.v("b"));
                    pi(c3, path_ab, "p", |c4| eq_app(u.clone(), c4.v("A"), c4.v("a"), c4.v("b")))
                })
            })
        });
        let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
            lam(c1, c1.v("A"), "a", |c2| {
                lam(c2, c2.v("A"), "b", |c3| {
                    let path_ab = Term::path(c3.v("A"), c3.v("a"), c3.v("b"));
                    lam(c3, path_ab, "p", |c4| {
                        cubical::path_to_eq(u.clone(), &c4.v("A"), &c4.v("a"), &c4.v("p"))
                    })
                })
            })
        });
        install(env, "path_to_eq", 1, ty, value)?;
    }

    // ---- eq_to_path.{u} : Pi (A:Sort u)(a b:A)(h:Eq A a b). Path A a b ---------
    {
        let u = Level::param(0);
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, c1.v("A"), "a", |c2| {
                pi(c2, c2.v("A"), "b", |c3| {
                    let eq_ab = eq_app(u.clone(), c3.v("A"), c3.v("a"), c3.v("b"));
                    pi(c3, eq_ab, "h", |c4| Term::path(c4.v("A"), c4.v("a"), c4.v("b")))
                })
            })
        });
        let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
            lam(c1, c1.v("A"), "a", |c2| {
                lam(c2, c2.v("A"), "b", |c3| {
                    let eq_ab = eq_app(u.clone(), c3.v("A"), c3.v("a"), c3.v("b"));
                    lam(c3, eq_ab, "h", |c4| {
                        cubical::eq_to_path(u.clone(), &c4.v("A"), &c4.v("a"), &c4.v("b"), &c4.v("h"))
                    })
                })
            })
        });
        install(env, "eq_to_path", 1, ty, value)?;
    }

    Ok(())
}

/// Install `ua.{u} : Π (A B : Sort u) (e : Equiv A B). Path (Sort u) A B` — see
/// [`rv_kernel_core::glue::ua`]/`ua_ty`. This states univalence: `ua e` really is
/// a `Path` between `A` and `B`, and it type-checks by the ordinary `Checker` like
/// every other installed constant here. What it does **not** give is the
/// *computation rule* `transport (ua e) a ↝ e.f a` — `ua`'s underlying `Glue`
/// term is soundly *stuck* under `transport`/`hcomp` (no Kan-correction term for
/// it exists yet; see `docs/cubical.md`'s "Known limitation" and
/// `rv_kernel_core::kan`'s Phase 3.12–3.14 notes). Requires `Equiv`/`idEquiv`
/// ([`rv_kernel_core::equiv::declare_equiv`]) to already be installed.
pub fn install_ua(env: &mut Env) -> Result<(), String> {
    if !env.contains("Equiv") || !env.contains("idEquiv") {
        return Err("'ua' requires 'Equiv'/'idEquiv' to already be installed".to_string());
    }
    let root = Ctx(vec![]);
    let u = Level::param(0);
    let equiv_ab = |c: &Ctx| Term::apps(Term::cnst(name("Equiv"), vec![u.clone()]), [c.v("A"), c.v("B")]);
    let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
        pi(c1, Term::Sort(u.clone()), "B", |c2| {
            let ety = equiv_ab(c2);
            pi(c2, ety, "e", |c3| rv_kernel_core::glue::ua_ty(u.clone(), c3.v("A"), c3.v("B")))
        })
    });
    let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
        lam(c1, Term::Sort(u.clone()), "B", |c2| {
            let ety = equiv_ab(c2);
            lam(c2, ety, "e", |c3| rv_kernel_core::glue::ua(u.clone(), c3.v("A"), c3.v("B"), c3.v("e")))
        })
    });
    install(env, "ua", 1, ty, value)
}

/// Install the by-name-callable **equivalence-algebra** constants from
/// [`rv_kernel_core::equiv`]: `idToEquiv` (the canonical `Path Type A B → Equiv A
/// B` map, [`rv_kernel_core::equiv::id_to_equiv`]), `symEquiv`
/// ([`rv_kernel_core::equiv::sym_equiv`]), `compEquiv`
/// ([`rv_kernel_core::equiv::comp_equiv`]), and the `Univalence` statement itself
/// ([`rv_kernel_core::equiv::univalence_ty`]) — installed as a `Type`-valued
/// constant (its *value* is the stated `Type`, not a proof inhabiting it; see
/// that function's doc for exactly what's open). Requires `Equiv`/`idEquiv`
/// ([`rv_kernel_core::equiv::declare_equiv`]), `IsContr`
/// ([`rv_kernel_core::contr::declare_is_contr`]), and `Fiber2`
/// ([`rv_kernel_core::contr::declare_fiber2`]) to already be installed.
pub fn install_equiv_algebra(env: &mut Env) -> Result<(), String> {
    for n in ["Equiv", "idEquiv", "IsContr", "Fiber2"] {
        if !env.contains(n) {
            return Err(format!("'idToEquiv'/'symEquiv'/'compEquiv'/'Univalence' require '{n}' to already be installed"));
        }
    }
    let root = Ctx(vec![]);
    let u = Level::param(0);
    let equiv_ty = |c: &Ctx, a: &str, b: &str| Term::apps(Term::cnst(name("Equiv"), vec![u.clone()]), [c.v(a), c.v(b)]);

    // ---- idToEquiv.{u} : Pi (A B:Sort u)(p:Path (Sort u) A B). Equiv A B ----
    {
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, Term::Sort(u.clone()), "B", |c2| {
                let path_ab = Term::path(Term::Sort(u.clone()), c2.v("A"), c2.v("B"));
                pi(c2, path_ab, "p", |c3| equiv_ty(c3, "A", "B"))
            })
        });
        let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
            lam(c1, Term::Sort(u.clone()), "B", |c2| {
                let path_ab = Term::path(Term::Sort(u.clone()), c2.v("A"), c2.v("B"));
                lam(c2, path_ab, "p", |c3| {
                    rv_kernel_core::equiv::id_to_equiv(u.clone(), &c3.v("A"), &c3.v("B"), &c3.v("p"))
                })
            })
        });
        install(env, "idToEquiv", 1, ty, value)?;
    }

    // ---- symEquiv.{u} : Pi (A B:Sort u)(e:Equiv A B). Equiv B A ----
    {
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, Term::Sort(u.clone()), "B", |c2| {
                let eab = equiv_ty(c2, "A", "B");
                pi(c2, eab, "e", |c3| Term::apps(Term::cnst(name("Equiv"), vec![u.clone()]), [c3.v("B"), c3.v("A")]))
            })
        });
        let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
            lam(c1, Term::Sort(u.clone()), "B", |c2| {
                let eab = equiv_ty(c2, "A", "B");
                lam(c2, eab, "e", |c3| {
                    rv_kernel_core::equiv::sym_equiv(u.clone(), &c3.v("A"), &c3.v("B"), &c3.v("e"))
                })
            })
        });
        install(env, "symEquiv", 1, ty, value)?;
    }

    // ---- compEquiv.{u} : Pi (A B C:Sort u)(e1:Equiv A B)(e2:Equiv B C). Equiv A C ----
    {
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, Term::Sort(u.clone()), "B", |c2| {
                pi(c2, Term::Sort(u.clone()), "C", |c3| {
                    let eab = equiv_ty(c3, "A", "B");
                    pi(c3, eab, "e1", |c4| {
                        let ebc = equiv_ty(c4, "B", "C");
                        pi(c4, ebc, "e2", |c5| {
                            Term::apps(Term::cnst(name("Equiv"), vec![u.clone()]), [c5.v("A"), c5.v("C")])
                        })
                    })
                })
            })
        });
        let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
            lam(c1, Term::Sort(u.clone()), "B", |c2| {
                lam(c2, Term::Sort(u.clone()), "C", |c3| {
                    let eab = equiv_ty(c3, "A", "B");
                    lam(c3, eab, "e1", |c4| {
                        let ebc = equiv_ty(c4, "B", "C");
                        lam(c4, ebc, "e2", |c5| {
                            rv_kernel_core::equiv::comp_equiv(
                                u.clone(),
                                &c5.v("A"),
                                &c5.v("B"),
                                &c5.v("C"),
                                &c5.v("e1"),
                                &c5.v("e2"),
                            )
                        })
                    })
                })
            })
        });
        install(env, "compEquiv", 1, ty, value)?;
    }

    // ---- Univalence : Type1 := the univalence statement, fixed at level 0 ------
    //
    // `rv_kernel_core::equiv::univalence_ty` is level-polymorphic (`Univalence.{u}`),
    // but `rv-syntax`'s surface grammar has no explicit universe-level-argument
    // syntax (`Name.{u}`) — only levels *inferable* from an applied argument's own
    // checked sort (e.g. `Equiv(A, B)`'s level comes from `A`/`B`'s sort). `Univalence`
    // has no term argument to infer a level from, so a universe-polymorphic
    // installation would be permanently unreachable by name from `.rv` (the
    // elaborator's own error is literally "supply N level argument(s) as N.{…}",
    // syntax `rv-syntax` does not parse). Installed monomorphically at level 0
    // instead — `Univalence : Type1`, the base-universe instance — so it is usable
    // as an ordinary bare name (e.g. `axiom u : Univalence`), at the cost of the
    // (Rust-side-only) polymorphism `univalence_ty` itself still offers.
    {
        let lvl0 = Level::of_nat(0);
        let succ0 = Level::succ(lvl0.clone());
        let ty = Term::Sort(succ0);
        let value = rv_kernel_core::equiv::univalence_ty(lvl0);
        install(env, "Univalence", 0, ty, value)?;
    }

    // ---- apId.{u} : Pi (ty:Sort u)(a b:ty)(p:Path ty a b). Path (Path ty a b) (ap id p) p
    {
        let ty = pi(&root, Term::Sort(u.clone()), "ty", |c1| {
            pi(c1, c1.v("ty"), "a", |c2| {
                pi(c2, c2.v("ty"), "b", |c3| {
                    let path_ab = Term::path(c3.v("ty"), c3.v("a"), c3.v("b"));
                    pi(c3, path_ab, "p", |c4| {
                        let path_ab4 = Term::path(c4.v("ty"), c4.v("a"), c4.v("b"));
                        let id_ty = Term::lam(c4.v("ty"), Term::Var(0));
                        let ap_id_p = rv_kernel_core::cubical::ap(&id_ty, &c4.v("p"));
                        Term::path(path_ab4, ap_id_p, c4.v("p"))
                    })
                })
            })
        });
        let value = lam(&root, Term::Sort(u.clone()), "ty", |c1| {
            lam(c1, c1.v("ty"), "a", |c2| {
                lam(c2, c2.v("ty"), "b", |c3| {
                    let path_ab = Term::path(c3.v("ty"), c3.v("a"), c3.v("b"));
                    lam(c3, path_ab, "p", |c4| {
                        rv_kernel_core::equiv::ap_id(&c4.v("ty"), &c4.v("a"), &c4.v("b"), &c4.v("p"))
                    })
                })
            })
        });
        install(env, "apId", 1, ty, value)?;
    }

    // ---- apComp.{u} : Pi (A B C:Sort u)(f:A->B)(g:B->C)(x y:A)(p:Path A x y).
    //        Path (Path C (g (f x)) (g (f y))) (ap (g.f) p) (ap g (ap f p))
    {
        // Built entirely via `Ctx::v` name lookups (which compute the correct
        // de Bruijn index for the context depth they're called at on their own)
        // rather than manual `.lift(..)` arithmetic — matches this module's other
        // deeply-nested constants (e.g. `ptrans` above) and avoids exactly the
        // off-by-N lift bugs manual index-juggling invites.
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, Term::Sort(u.clone()), "B", |c2| {
                pi(c2, Term::Sort(u.clone()), "C", |c3| {
                    let fty = Term::arrow(c3.v("A"), c3.v("B"));
                    pi(c3, fty, "f", |c4| {
                        let gty = Term::arrow(c4.v("B"), c4.v("C"));
                        pi(c4, gty, "g", |c5| {
                            pi(c5, c5.v("A"), "x", |c6| {
                                pi(c6, c6.v("A"), "y", |c7| {
                                    let path_xy = Term::path(c7.v("A"), c7.v("x"), c7.v("y"));
                                    pi(c7, path_xy, "p", |c8| {
                                        let fx = Term::app(c8.v("f"), c8.v("x"));
                                        let fy = Term::app(c8.v("f"), c8.v("y"));
                                        let gfx = Term::app(c8.v("g"), fx);
                                        let gfy = Term::app(c8.v("g"), fy);
                                        let inner = Term::path(c8.v("C"), gfx, gfy);
                                        // gof := λ (z:A). g (f z), built inside a fresh binder
                                        // one level under c8, so `f`/`g` are looked up via
                                        // `c9.v(..)` at THAT depth.
                                        let gof = lam(c8, c8.v("A"), "z", |c9| {
                                            Term::app(c9.v("g"), Term::app(c9.v("f"), c9.v("z")))
                                        });
                                        let ap_gof_p = rv_kernel_core::cubical::ap(&gof, &c8.v("p"));
                                        let ap_f_p = rv_kernel_core::cubical::ap(&c8.v("f"), &c8.v("p"));
                                        let ap_g_ap_f_p = rv_kernel_core::cubical::ap(&c8.v("g"), &ap_f_p);
                                        Term::path(inner, ap_gof_p, ap_g_ap_f_p)
                                    })
                                })
                            })
                        })
                    })
                })
            })
        });
        let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
            lam(c1, Term::Sort(u.clone()), "B", |c2| {
                lam(c2, Term::Sort(u.clone()), "C", |c3| {
                    let fty = Term::arrow(c3.v("A"), c3.v("B"));
                    lam(c3, fty, "f", |c4| {
                        let gty = Term::arrow(c4.v("B"), c4.v("C"));
                        lam(c4, gty, "g", |c5| {
                            lam(c5, c5.v("A"), "x", |c6| {
                                lam(c6, c6.v("A"), "y", |c7| {
                                    let path_xy = Term::path(c7.v("A"), c7.v("x"), c7.v("y"));
                                    lam(c7, path_xy, "p", |c8| {
                                        rv_kernel_core::equiv::ap_comp(
                                            &c8.v("A"),
                                            &c8.v("B"),
                                            &c8.v("C"),
                                            &c8.v("f"),
                                            &c8.v("g"),
                                            &c8.v("x"),
                                            &c8.v("y"),
                                            &c8.v("p"),
                                        )
                                    })
                                })
                            })
                        })
                    })
                })
            })
        });
        install(env, "apComp", 1, ty, value)?;
    }

    // ---- symEquivInv.{u} : Pi (A B:Sort u)(e:Equiv A B). Path (Equiv A B) (symEquiv B A (symEquiv A B e)) e
    {
        let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
            pi(c1, Term::Sort(u.clone()), "B", |c2| {
                let eab = equiv_ty(c2, "A", "B");
                pi(c2, eab, "e", |c3| {
                    let sym1 = rv_kernel_core::equiv::sym_equiv(u.clone(), &c3.v("A"), &c3.v("B"), &c3.v("e"));
                    let sym2 = rv_kernel_core::equiv::sym_equiv(u.clone(), &c3.v("B"), &c3.v("A"), &sym1);
                    Term::path(equiv_ty(c3, "A", "B"), sym2, c3.v("e"))
                })
            })
        });
        let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
            lam(c1, Term::Sort(u.clone()), "B", |c2| {
                let eab = equiv_ty(c2, "A", "B");
                lam(c2, eab, "e", |c3| {
                    rv_kernel_core::equiv::sym_equiv_inv(u.clone(), &c3.v("A"), &c3.v("B"), &c3.v("e"))
                })
            })
        });
        install(env, "symEquivInv", 1, ty, value)?;
    }

    // ---- compEquivIdL_f/_g, compEquivIdR_f/_g : compEquiv's unit laws (field-level) ----
    {
        // Shared shape: Pi (A B:Sort u)(e:Equiv A B). Path (<field ty>) (<field
        // of compEquiv .. e>) (<field of e>) — `mk_ty` picks `A->B` for the `f`
        // field, `B->A` for the `g` field; `mk_lhs_l`/`mk_lhs_r` pick the left-unit
        // (`idEquiv A` on the left leg) vs right-unit (`idEquiv B` on the right leg)
        // shape via `equiv::comp_equiv_id_{l,r}_{f,g}` directly.
        type Builder = fn(Level, &Term, &Term, &Term) -> Term;
        let laws: [(&str, Builder, bool); 4] = [
            ("compEquivIdL_f", rv_kernel_core::equiv::comp_equiv_id_l_f as Builder, true),
            ("compEquivIdL_g", rv_kernel_core::equiv::comp_equiv_id_l_g as Builder, false),
            ("compEquivIdR_f", rv_kernel_core::equiv::comp_equiv_id_r_f as Builder, true),
            ("compEquivIdR_g", rv_kernel_core::equiv::comp_equiv_id_r_g as Builder, false),
        ];
        for (nm, build, is_f) in laws {
            // The stated type's endpoints use the *plain field projection*
            // `Equiv.f e`/`Equiv.g e` on both sides — `build(..)` itself returns
            // `refl X` where `X` is the (defeq-but-not-syntactically-equal)
            // `compEquiv`-projected field (see e.g. `comp_equiv_id_l_f`'s doc:
            // "closed by plain `refl` + the checker's Π-η"), so `install`'s
            // `Checker::check` accepts this stated type by reducing both to the
            // same normal form.
            let ty = pi(&root, Term::Sort(u.clone()), "A", |c1| {
                pi(c1, Term::Sort(u.clone()), "B", |c2| {
                    let eab = equiv_ty(c2, "A", "B");
                    pi(c2, eab, "e", |c3| {
                        let field_ty =
                            if is_f { Term::arrow(c3.v("A"), c3.v("B")) } else { Term::arrow(c3.v("B"), c3.v("A")) };
                        let field = if is_f { "Equiv.f" } else { "Equiv.g" };
                        let ef = Term::apps(Term::cnst(name(field), vec![u.clone()]), [c3.v("A"), c3.v("B"), c3.v("e")]);
                        Term::path(field_ty, ef.clone(), ef)
                    })
                })
            });
            let value = lam(&root, Term::Sort(u.clone()), "A", |c1| {
                lam(c1, Term::Sort(u.clone()), "B", |c2| {
                    let eab = equiv_ty(c2, "A", "B");
                    lam(c2, eab, "e", |c3| build(u.clone(), &c3.v("A"), &c3.v("B"), &c3.v("e")))
                })
            });
            install(env, nm, 1, ty, value)?;
        }
    }

    Ok(())
}
