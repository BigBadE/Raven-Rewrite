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

    fn check_usage(&self, n: &str) -> Result<(), String> {
        match self.env().get(n) {
            Some(Decl::Def { ty, value, .. }) => {
                crate::graded::check_usage_against(self.env(), value, ty).map_err(|e| format!("definition '{n}': {e}"))
            }
            _ => Ok(()), // axioms/inductives/etc. carry no value to check usage of.
        }
    }
}
