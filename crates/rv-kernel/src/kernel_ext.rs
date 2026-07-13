//! The untrusted extension surface of [`rv_kernel_core::Kernel`].
//!
//! [`rv_kernel_core::kernel`]'s doc comment explains why these live here instead of
//! as inherent methods on `Kernel`: inductive/coinductive declaration and the fixed
//! axiomatic-schema installers all bottom out in *synthesis* or *derivation* logic
//! (recursor generation, mutual-block elaboration, a proof-term construction for
//! `funext`, a QTT usage linter) that is UNTRUSTED per the crate-level trust map in
//! `lib.rs` — it must not live in `rv-kernel-core`, or that crate would gain a
//! dependency back on `rv-kernel`, breaking the one-way trust boundary the split
//! exists to enforce.
//!
//! [`KernelExt`] restores the pre-split call-site ergonomics (`k.declare_inductive(..)`
//! etc.) via an extension trait implemented for `rv_kernel_core::Kernel`, built only
//! out of that crate's public API — chiefly [`rv_kernel_core::Kernel::env_mut`], the
//! same sanctioned mutation point `Kernel`'s own inherent methods use. Every one of
//! these calls still terminates in a raw [`rv_kernel_core::env::Env::insert`] of an
//! axiomatic schema constant or a shape-checked recursor (see the "Bypasses of the
//! checked front door" section of `lib.rs`'s trust map) — that has not changed, only
//! which crate the call site lives in.

use rv_kernel_core::env::Decl;
use rv_kernel_core::Kernel;

use crate::generate::{declare_inductive, IndSpec};

/// Extension trait providing the untrusted schema-installer/synthesis methods on top
/// of [`rv_kernel_core::Kernel`]'s trusted front door. Bring this trait into scope
/// (`use rv_kernel::KernelExt;`) wherever the pre-split `Kernel::declare_inductive`-
/// style method calls are used.
pub trait KernelExt {
    /// Declare an inductive family.
    fn declare_inductive(&mut self, spec: IndSpec) -> Result<(), String>;

    /// Declare a **mutual** group of inductive families simultaneously.
    fn declare_mutual(&mut self, specs: Vec<IndSpec>) -> Result<(), String>;

    /// Declare a **coinductive** ("codata") family: a greatest fixpoint given by its
    /// destructors, with a generated corecursor (see [`rv_kernel_core::coinductive`]).
    fn declare_coinductive(&mut self, spec: rv_kernel_core::coinductive::CoindSpec) -> Result<(), String>;

    /// Install the fixed **quotient** schema (`Quot`, `Quot.mk`, `Quot.sound`,
    /// `Quot.lift`, `Quot.ind`). Requires the `Eq` inductive to already be present. See
    /// [`rv_kernel_core::quotient`] for the types and the soundness argument.
    fn install_quot(&mut self) -> Result<(), String>;

    /// Install the fixed **propositional-truncation** higher-inductive schema (`Trunc`,
    /// `Trunc.tr`, `Trunc.eq`, `Trunc.lift`, `Trunc.ind`). Requires the `Eq` inductive to
    /// already be present. See [`rv_kernel_core::trunc`] for the types and the
    /// soundness argument.
    fn install_trunc(&mut self) -> Result<(), String>;

    /// Install `funext` — function extensionality — **derived** from `Quot`/`Quot.sound`/
    /// `Quot.lift` (requires [`KernelExt::install_quot`] first) plus this kernel's
    /// already-definitional η-conversion. See [`crate::funext`] for the statement and
    /// proof.
    fn install_funext(&mut self) -> Result<(), String>;

    /// Install the fixed **interval HIT** schema (`I2`, `I2.zero`, `I2.one`,
    /// `I2.seg`, `I2.rec`) — see [`rv_kernel_core::interval_hit`].
    fn install_interval_hit(&mut self) -> Result<(), String>;

    /// Install the surfaced **cubical layer**: interval literals/connections
    /// (`i0`/`i1`/`ineg`/`imeet`/`ijoin`), `Path`/`PathP`/`plam`/`papp`, and the
    /// derived operators `refl`/`ap`/`pfunext`/`transport`/`subst`/`J`/`trans`/
    /// `path_to_eq`/`eq_to_path` — see [`crate::cubical_surface`]. Requires `Eq` to
    /// already be declared.
    fn install_cubical(&mut self) -> Result<(), String>;

    /// Install the **cubical circle** `S1c` (a genuinely-computing self-loop HIT:
    /// `S1c`/`S1c.base`/`S1c.loop`/`S1c.rec`) — see
    /// [`rv_kernel_core::circle_cubical`].
    fn install_s1c(&mut self) -> Result<(), String>;

    /// Install the **cubical sphere** `S²` (one nullary point `S2.base` plus one
    /// `S2.surf : Path (Path S2 base base) (refl base) (refl base)` 2-cell,
    /// generated via [`rv_kernel_core::cubical_hit::declare_cubical_hit`]'s "S²"
    /// higher-path support) plus its recursor `S2.rec`.
    fn install_s2(&mut self) -> Result<(), String>;

    /// Install the **cubical torus** `T²` (one nullary point `T2.base`, two
    /// distinct self-loops `T2.loopP`/`T2.loopQ`, and a square `T2.surf : PathP
    /// (λi. Path T2 (loopP@i) (loopP@i)) loopQ loopQ` — the textbook `l = r`,
    /// `top = bottom` cubical presentation) plus its recursor `T2.rec`. See
    /// [`rv_kernel_core::cubical_hit::CubSurfSpec`]'s doc comment for the general
    /// square schema this is built from.
    fn install_torus(&mut self) -> Result<(), String>;

    /// Install the **cubical 3-sphere** `S³` (one nullary point `S3.base` plus one
    /// fully-degenerate 3-cell `S3.cube`, generated via
    /// [`rv_kernel_core::cubical_hit::CubCubeSpec::s3`]) plus its recursor
    /// `S3.rec`.
    fn install_s3(&mut self) -> Result<(), String>;

    /// Install a worked **set-quotient-style HIT** `SetQ` — a genuinely cubical,
    /// computing analogue of `Quot`'s propositional quotient (per
    /// [`KernelExt::declare_cubical_hit`]'s doc comment). Declares a dedicated
    /// two-point domain `SQDom` (`SQDom.a`/`SQDom.b`), the "collapse everything"
    /// relation `SQDom.R : SQDom -> SQDom -> Type 0 := λ _ _. True` (mirroring
    /// `examples/proofs/quotient_demo.rv`'s `AlwaysR`), and then `SetQ`/`SetQ.mk :
    /// SQDom -> SetQ`/`SetQ.glue : Π (a b : SQDom) (h : SQDom.R a b), Path SetQ
    /// (mk a) (mk b)`/`SetQ.rec`. Unlike `Quot.sound`, `SetQ.glue` is a genuinely
    /// cubical path constructor: `SetQ.rec`'s ι-rule actually *reduces* on
    /// `glue a b h @ i`, not merely typechecks propositionally.
    fn install_set_quotient(&mut self) -> Result<(), String>;

    /// Declare a general cubical higher-inductive type from `spec` — see
    /// [`rv_kernel_core::cubical_hit::declare_cubical_hit`]/[`rv_kernel_core::cubical_hit::CubHitSpec`].
    /// This is the general escape hatch [`KernelExt::install_s1c`]/
    /// [`KernelExt::install_s2`] are themselves built from; it is also how a
    /// **set-quotient-style HIT** is declared — e.g. a HIT with one fielded point
    /// constructor `mk : A -> Q` and one quantified path constructor `eq : Π (a b :
    /// A) (h : R a b). Path Q (mk a) (mk b)` (mirroring `Quot`'s shape, but as a
    /// genuinely cubical/computing path instead of `Quot.sound`'s propositional
    /// one) is exactly one `CubHitSpec` with those `points`/`paths` fields.
    fn declare_cubical_hit(&mut self, spec: &rv_kernel_core::cubical_hit::CubHitSpec) -> Result<(), String>;

    /// Install the **bi-invertible equivalence** type `Equiv A B` (`Equiv`/
    /// `Equiv.mk`/`Equiv.rec`/`Equiv.f`/`Equiv.g`/`Equiv.sec`/`Equiv.ret`) plus
    /// `idEquiv` — see [`rv_kernel_core::equiv`].
    fn install_equiv(&mut self) -> Result<(), String>;

    /// Install `IsContr`/`Fiber`/`IsEquiv`/`idIsEquiv` — the contractible-fibers
    /// equivalence notion (HoTT book §4.2/§4.4) — see [`rv_kernel_core::contr`].
    fn install_contr(&mut self) -> Result<(), String>;

    /// Install `IsHAE`/`idHAE` — the half-adjoint equivalence notion (HoTT book
    /// §4.2.1) — see [`rv_kernel_core::equiv_hae`].
    fn install_hae(&mut self) -> Result<(), String>;

    /// Install `ua : Π (A B : Sort u) (e : Equiv A B). Path (Sort u) A B` —
    /// univalence, *stated* (not computational — `transport (ua e) x` does not
    /// reduce to `e.f x`; see `docs/cubical.md`'s "Known limitation") — as an
    /// ordinary by-name-callable constant. Requires [`KernelExt::install_equiv`]
    /// first. See [`rv_kernel_core::glue::ua`]/`ua_ty`.
    fn install_ua(&mut self) -> Result<(), String>;

    /// Check the QTT usage discipline (`crate::graded`) of the stored definition
    /// `name`: a graded binder (linear `1`/erased `0`) in its type must be used
    /// accordingly in its value. Ungraded (`ω`, the default) binders always pass, so
    /// this only ever rejects code that actually opts into a grade annotation — it is
    /// **not** run automatically by `Kernel::add_definition` (existing callers, and the
    /// `graded` module's own unit tests, rely on `add_definition` alone never enforcing
    /// usage). The surface layer (the `fun`/`forall` graded-binder syntax) calls this
    /// explicitly after elaborating each proof-fragment declaration.
    fn check_usage(&self, n: &str) -> Result<(), String>;
}

impl KernelExt for Kernel {
    fn declare_inductive(&mut self, spec: IndSpec) -> Result<(), String> {
        declare_inductive(self.env_mut(), spec)
    }

    fn declare_mutual(&mut self, specs: Vec<IndSpec>) -> Result<(), String> {
        crate::mutual::declare_mutual(self.env_mut(), specs)
    }

    fn declare_coinductive(&mut self, spec: rv_kernel_core::coinductive::CoindSpec) -> Result<(), String> {
        rv_kernel_core::coinductive::declare_coinductive(self.env_mut(), spec)
    }

    fn install_quot(&mut self) -> Result<(), String> {
        rv_kernel_core::quotient::install_quot(self.env_mut())
    }

    fn install_trunc(&mut self) -> Result<(), String> {
        rv_kernel_core::trunc::install_trunc(self.env_mut())
    }

    fn install_funext(&mut self) -> Result<(), String> {
        crate::funext::install_funext(self.env_mut())
    }

    fn install_interval_hit(&mut self) -> Result<(), String> {
        rv_kernel_core::interval_hit::install_interval_hit(self.env_mut())
    }

    fn install_cubical(&mut self) -> Result<(), String> {
        crate::cubical_surface::install_cubical(self.env_mut())
    }

    fn install_s1c(&mut self) -> Result<(), String> {
        rv_kernel_core::circle_cubical::install_circle_cubical(self.env_mut())
    }

    fn install_s2(&mut self) -> Result<(), String> {
        use rv_kernel_core::cubical_hit::{CubHitSpec, CubPointSpec, CubSurfSpec};
        let spec = CubHitSpec {
            name: "S2".to_string(),
            points: vec![CubPointSpec::nullary("S2.base")],
            paths: vec![],
            surfaces: vec![CubSurfSpec::s2("S2.surf", 0)],
            cubes: vec![],
            hypers: vec![],
        };
        rv_kernel_core::cubical_hit::declare_cubical_hit(self.env_mut(), &spec)
    }

    fn declare_cubical_hit(&mut self, spec: &rv_kernel_core::cubical_hit::CubHitSpec) -> Result<(), String> {
        rv_kernel_core::cubical_hit::declare_cubical_hit(self.env_mut(), spec)
    }

    fn install_torus(&mut self) -> Result<(), String> {
        use rv_kernel_core::cubical_hit::{CubHitSpec, CubPathSpec, CubPointSpec, CubSurfSpec};
        let spec = CubHitSpec {
            name: "T2".to_string(),
            points: vec![CubPointSpec::nullary("T2.base")],
            paths: vec![CubPathSpec::simple("T2.loopP", 0, 0), CubPathSpec::simple("T2.loopQ", 0, 0)],
            surfaces: vec![CubSurfSpec {
                name: "T2.surf".to_string(),
                base: 0,
                left: Some(0),
                right: Some(0),
                top: Some(1),
                bottom: Some(1),
            }],
            cubes: vec![],
            hypers: vec![],
        };
        rv_kernel_core::cubical_hit::declare_cubical_hit(self.env_mut(), &spec)
    }

    fn install_s3(&mut self) -> Result<(), String> {
        use rv_kernel_core::cubical_hit::{CubCubeSpec, CubHitSpec, CubPointSpec};
        let spec = CubHitSpec {
            name: "S3".to_string(),
            points: vec![CubPointSpec::nullary("S3.base")],
            paths: vec![],
            surfaces: vec![],
            cubes: vec![CubCubeSpec::s3("S3.cube", 0)],
            hypers: vec![],
        };
        rv_kernel_core::cubical_hit::declare_cubical_hit(self.env_mut(), &spec)
    }

    fn install_set_quotient(&mut self) -> Result<(), String> {
        use rv_kernel_core::cubical_hit::{CubHitSpec, CubPathSpec, CubPointSpec, Field};
        use rv_kernel_core::term::{name, Term};

        // A dedicated two-point domain `SQDom` for this worked example — a name
        // unlikely to collide with any user-declared `.rv` `enum`, since this
        // installer runs before any user source (or `RAVEN_PRELUDE`, which
        // declares no types of its own) is parsed.
        let dom_spec = IndSpec {
            name: name("SQDom"),
            num_levels: 0,
            ty: Term::typ(0),
            num_params: 0,
            ctors: vec![
                crate::generate::CtorSpec { name: name("SQDom.a"), ty: Term::cnst(name("SQDom"), vec![]) },
                crate::generate::CtorSpec { name: name("SQDom.b"), ty: Term::cnst(name("SQDom"), vec![]) },
            ],
            rec_name: name("SQDom.rec"),
        };
        declare_inductive(self.env_mut(), dom_spec)?;

        // The "collapse everything" relation `SQDom.R : SQDom -> SQDom -> Type 0 :=
        // λ _ _. True` — mirrors `examples/proofs/quotient_demo.rv`'s `AlwaysR`, but
        // here backs a genuinely cubical/computing quotient path (`SetQ.glue`)
        // instead of `Quot.sound`'s propositional one.
        let dom = Term::cnst(name("SQDom"), vec![]);
        let true_ty = Term::cnst(name("True"), vec![]);
        let r_ty = Term::pi(dom.clone(), Term::pi(dom.clone(), Term::prop()));
        let r_val = Term::lam(dom.clone(), Term::lam(dom.clone(), true_ty));
        self.env_mut().insert(name("SQDom.R"), Decl::Def { num_levels: 0, ty: r_ty, value: r_val })?;

        // `SetQ.mk : SQDom -> SetQ`, `SetQ.glue : Π (a b : SQDom) (h : SQDom.R a b),
        // Path SetQ (mk a) (mk b)`.
        let spec = CubHitSpec {
            name: "SetQ".to_string(),
            points: vec![CubPointSpec { name: "SetQ.mk".to_string(), fields: vec![Field::NonRec(dom.clone())] }],
            paths: vec![CubPathSpec {
                name: "SetQ.glue".to_string(),
                // Π (a b : SQDom) (h : SQDom.R a b), .. — innermost = h = Var(0).
                quantifiers: vec![
                    dom.clone(),
                    dom.clone(),
                    Term::apps(Term::cnst(name("SQDom.R"), vec![]), [Term::Var(1), Term::Var(0)]),
                ],
                lhs: (0, vec![Term::Var(2)]),
                rhs: (0, vec![Term::Var(1)]),
            }],
            surfaces: vec![],
            cubes: vec![],
            hypers: vec![],
        };
        rv_kernel_core::cubical_hit::declare_cubical_hit(self.env_mut(), &spec)
    }

    fn install_equiv(&mut self) -> Result<(), String> {
        rv_kernel_core::equiv::declare_equiv(self.env_mut())
    }

    fn install_contr(&mut self) -> Result<(), String> {
        rv_kernel_core::contr::declare_is_contr(self.env_mut())?;
        rv_kernel_core::contr::declare_fiber(self.env_mut())?;
        rv_kernel_core::contr::declare_is_equiv(self.env_mut())
    }

    fn install_hae(&mut self) -> Result<(), String> {
        rv_kernel_core::equiv_hae::declare_is_hae(self.env_mut())
    }

    fn install_ua(&mut self) -> Result<(), String> {
        crate::cubical_surface::install_ua(self.env_mut())
    }

    fn check_usage(&self, n: &str) -> Result<(), String> {
        match self.env().get(n) {
            Some(Decl::Def { ty, value, .. }) => {
                crate::graded::check_usage_against(self.env(), value, ty).map_err(|e| format!("definition '{n}': {e}"))
            }
            _ => Ok(()), // axioms/inductives/etc. carry no value to check usage of.
        }
    }
}
