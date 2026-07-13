//! `rv-kernel-core` — the compiler-enforced trusted core of the Raven kernel.
//!
//! This crate is the physically-extracted TRUSTED slice described in
//! `rv_kernel`'s crate-level "Trust map" doc comment: the term representation, the
//! bidirectional type-checker, β/δ/ζ/ι/ν reduction (both a direct reducer and an
//! NbE engine), the declaration environment, the *typing and reduction rules* of
//! the axiomatically-declared schemas (`Quot`, `Trunc`, the circle HIT, general
//! HITs, coinductives), the shape-checking of inductive families
//! (`inductive::declare_raw`), and the [`kernel::Kernel`] front door
//! (`add_axiom`/`add_definition`/`check`/`infer`/`recheck_all_definitions`).
//!
//! **Dependency direction is enforced by the crate graph, not just documentation:**
//! this crate has zero dependency on `rv-kernel`. `rv-kernel` depends on
//! `rv-kernel-core` and contains everything UNTRUSTED — elaboration, unification,
//! tactic/proof-script execution, recursor *synthesis*, QTT usage-linting, erasure,
//! effects — all of which terminates in a call through this crate's checked front
//! door before anything it produces is trusted.
//!
//! See `rv_kernel`'s crate doc for the full trust-map narrative and exactly which
//! modules stayed behind (and why) despite being conceptually trusted.

pub mod check;
pub mod circle;
pub mod circle_cubical;
pub mod coinductive;
pub mod contr;
pub mod cubical;
pub mod env;
pub mod equiv;
pub mod face;
pub mod glue;
pub mod hit;
pub mod inductive;
pub mod interval_hit;
pub mod kan;
pub mod kernel;
pub mod level;
pub mod nbe;
pub mod quotient;
pub mod reduce;
pub mod term;
pub mod trunc;
pub mod util;

pub use check::{Checker, LocalCtx};
pub use env::{Decl, Env};
pub use kernel::{recheck_all_definitions, Kernel};
pub use level::Level;
pub use term::{name, Name, Term};
