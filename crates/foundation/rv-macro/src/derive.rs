//! Derive macro implementation
//!
//! This module implements automatic trait derivation for common traits:
//! - Copy
//! - Clone
//! - Debug
//! - PartialEq
//! - Eq
//! - Hash
//! - Default

use rv_intern::Symbol;
use rv_span::FileSpan;

/// Derive macro kind
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeriveMacro {
    /// #[derive(Copy)]
    Copy,
    /// #[derive(Clone)]
    Clone,
    /// #[derive(Debug)]
    Debug,
    /// #[derive(PartialEq)]
    PartialEq,
    /// #[derive(Eq)]
    Eq,
    /// #[derive(Hash)]
    Hash,
    /// #[derive(Default)]
    Default,
}

impl DeriveMacro {
    /// Parse a derive macro from its name
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "Copy" => Some(Self::Copy),
            "Clone" => Some(Self::Clone),
            "Debug" => Some(Self::Debug),
            "PartialEq" => Some(Self::PartialEq),
            "Eq" => Some(Self::Eq),
            "Hash" => Some(Self::Hash),
            "Default" => Some(Self::Default),
            _ => None,
        }
    }

    /// Get the trait name for this derive macro
    pub fn trait_name(&self) -> &'static str {
        match self {
            Self::Copy => "Copy",
            Self::Clone => "Clone",
            Self::Debug => "Debug",
            Self::PartialEq => "PartialEq",
            Self::Eq => "Eq",
            Self::Hash => "Hash",
            Self::Default => "Default",
        }
    }
}

/// Information about a struct or enum for derive macro generation
#[derive(Debug, Clone)]
pub struct DeriveInput {
    /// Type name
    pub name: Symbol,
    /// Fields (for structs) or variants (for enums)
    pub kind: DeriveInputKind,
    /// Source location
    pub span: FileSpan,
}

/// Kind of type being derived
#[derive(Debug, Clone)]
pub enum DeriveInputKind {
    /// Struct with named or unnamed fields
    Struct {
        /// Field names (None for tuple structs)
        fields: Vec<Option<Symbol>>,
    },
    /// Enum with variants
    Enum {
        /// Variant names and their fields
        variants: Vec<DeriveVariant>,
    },
}

/// Enum variant for derive macro
#[derive(Debug, Clone)]
pub struct DeriveVariant {
    /// Variant name
    pub name: Symbol,
    /// Field names (None for tuple variants)
    pub fields: Vec<Option<Symbol>>,
}

/// Generated trait implementation
#[derive(Debug, Clone)]
pub struct GeneratedImpl {
    /// Trait being implemented
    pub trait_name: Symbol,
    /// Type name
    pub type_name: Symbol,
    /// Generated method implementations (simplified as code strings)
    pub methods: Vec<GeneratedMethod>,
}

/// Generated method
#[derive(Debug, Clone)]
pub struct GeneratedMethod {
    /// Method name
    pub name: Symbol,
    /// Method implementation (simplified)
    pub body: String,
}

/// Derive macro generator
pub struct DeriveGenerator;

impl DeriveGenerator {
    /// Generate trait implementation for a derive macro
    pub fn generate(
        derive: DeriveMacro,
        input: &DeriveInput,
        interner: &rv_intern::Interner,
    ) -> Result<GeneratedImpl, DeriveError> {
        match derive {
            DeriveMacro::Copy => Self::generate_copy(input, interner),
            DeriveMacro::Clone => Self::generate_clone(input, interner),
            DeriveMacro::Debug => Self::generate_debug(input, interner),
            DeriveMacro::PartialEq => Self::generate_partial_eq(input, interner),
            DeriveMacro::Eq => Self::generate_eq(input, interner),
            DeriveMacro::Hash => Self::generate_hash(input, interner),
            DeriveMacro::Default => Self::generate_default(input, interner),
        }
    }

    /// Generate Copy implementation (marker trait, no methods)
    fn generate_copy(input: &DeriveInput, interner: &rv_intern::Interner) -> Result<GeneratedImpl, DeriveError> {
        Ok(GeneratedImpl {
            trait_name: interner.intern("Copy"),
            type_name: input.name,
            methods: Vec::new(), // Copy is a marker trait
        })
    }

    /// Generate Clone implementation
    fn generate_clone(input: &DeriveInput, interner: &rv_intern::Interner) -> Result<GeneratedImpl, DeriveError> {
        let clone_body = match &input.kind {
            DeriveInputKind::Struct { fields } => {
                if fields.is_empty() {
                    format!("Self {{}}")
                } else {
                    let field_clones: Vec<String> = fields
                        .iter()
                        .enumerate()
                        .map(|(i, field)| {
                            if let Some(name) = field {
                                let name_str = interner.resolve(name);
                                format!("{}: self.{}.clone()", name_str, name_str)
                            } else {
                                format!("self.{}.clone()", i)
                            }
                        })
                        .collect();
                    format!("Self {{ {} }}", field_clones.join(", "))
                }
            }
            DeriveInputKind::Enum { variants } => {
                // For enums, generate match with variant clones
                let variant_clones: Vec<String> = variants
                    .iter()
                    .map(|v| {
                        let v_name = interner.resolve(&v.name);
                        if v.fields.is_empty() {
                            format!("Self::{} => Self::{}", v_name, v_name)
                        } else {
                            let bindings: Vec<String> = v
                                .fields
                                .iter()
                                .enumerate()
                                .map(|(i, f)| {
                                    f.map_or_else(|| format!("f{}", i), |name| interner.resolve(&name).to_string())
                                })
                                .collect();
                            format!(
                                "Self::{}({}) => Self::{}({})",
                                v_name,
                                bindings.join(", "),
                                v_name,
                                bindings.iter().map(|b| format!("{}.clone()", b)).collect::<Vec<_>>().join(", ")
                            )
                        }
                    })
                    .collect();
                format!("match self {{ {} }}", variant_clones.join(", "))
            }
        };

        Ok(GeneratedImpl {
            trait_name: interner.intern("Clone"),
            type_name: input.name,
            methods: vec![GeneratedMethod {
                name: interner.intern("clone"),
                body: clone_body,
            }],
        })
    }

    /// Generate Debug implementation
    fn generate_debug(input: &DeriveInput, interner: &rv_intern::Interner) -> Result<GeneratedImpl, DeriveError> {
        let type_name = interner.resolve(&input.name);
        let debug_body = match &input.kind {
            DeriveInputKind::Struct { .. } => {
                format!("f.debug_struct(\"{}\").finish()", type_name)
            }
            DeriveInputKind::Enum { .. } => {
                format!("f.debug_tuple(\"{}\").finish()", type_name)
            }
        };

        Ok(GeneratedImpl {
            trait_name: interner.intern("Debug"),
            type_name: input.name,
            methods: vec![GeneratedMethod {
                name: interner.intern("fmt"),
                body: debug_body,
            }],
        })
    }

    /// Generate PartialEq implementation
    fn generate_partial_eq(input: &DeriveInput, interner: &rv_intern::Interner) -> Result<GeneratedImpl, DeriveError> {
        let eq_body = match &input.kind {
            DeriveInputKind::Struct { fields } => {
                if fields.is_empty() {
                    "true".to_string()
                } else {
                    let comparisons: Vec<String> = fields
                        .iter()
                        .enumerate()
                        .map(|(i, field)| {
                            if let Some(name) = field {
                                let name_str = interner.resolve(name);
                                format!("self.{} == other.{}", name_str, name_str)
                            } else {
                                format!("self.{} == other.{}", i, i)
                            }
                        })
                        .collect();
                    comparisons.join(" && ")
                }
            }
            DeriveInputKind::Enum { variants } => {
                // For enums, match both self and other
                let variant_comparisons: Vec<String> = variants
                    .iter()
                    .map(|v| {
                        let v_name = interner.resolve(&v.name);
                        if v.fields.is_empty() {
                            format!("(Self::{}, Self::{}) => true", v_name, v_name)
                        } else {
                            let bindings_self: Vec<String> = v
                                .fields
                                .iter()
                                .enumerate()
                                .map(|(i, _)| format!("s{}", i))
                                .collect();
                            let bindings_other: Vec<String> = v
                                .fields
                                .iter()
                                .enumerate()
                                .map(|(i, _)| format!("o{}", i))
                                .collect();
                            let comparisons: Vec<String> = (0..v.fields.len())
                                .map(|i| format!("s{} == o{}", i, i))
                                .collect();
                            format!(
                                "(Self::{}({}), Self::{}({})) => {}",
                                v_name,
                                bindings_self.join(", "),
                                v_name,
                                bindings_other.join(", "),
                                comparisons.join(" && ")
                            )
                        }
                    })
                    .collect();
                format!(
                    "match (self, other) {{ {}, _ => false }}",
                    variant_comparisons.join(", ")
                )
            }
        };

        Ok(GeneratedImpl {
            trait_name: interner.intern("PartialEq"),
            type_name: input.name,
            methods: vec![GeneratedMethod {
                name: interner.intern("eq"),
                body: eq_body,
            }],
        })
    }

    /// Generate Eq implementation (marker trait, requires PartialEq)
    fn generate_eq(input: &DeriveInput, interner: &rv_intern::Interner) -> Result<GeneratedImpl, DeriveError> {
        Ok(GeneratedImpl {
            trait_name: interner.intern("Eq"),
            type_name: input.name,
            methods: Vec::new(), // Eq is a marker trait
        })
    }

    /// Generate Hash implementation
    fn generate_hash(input: &DeriveInput, interner: &rv_intern::Interner) -> Result<GeneratedImpl, DeriveError> {
        let hash_body = match &input.kind {
            DeriveInputKind::Struct { fields } => {
                let field_hashes: Vec<String> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        if let Some(name) = field {
                            let name_str = interner.resolve(name);
                            format!("self.{}.hash(state);", name_str)
                        } else {
                            format!("self.{}.hash(state);", i)
                        }
                    })
                    .collect();
                field_hashes.join(" ")
            }
            DeriveInputKind::Enum { variants } => {
                let variant_hashes: Vec<String> = variants
                    .iter()
                    .enumerate()
                    .map(|(disc, v)| {
                        let v_name = interner.resolve(&v.name);
                        let mut stmts = vec![format!("{}.hash(state);", disc)];
                        if !v.fields.is_empty() {
                            let bindings: Vec<String> = v
                                .fields
                                .iter()
                                .enumerate()
                                .map(|(i, _)| format!("f{}", i))
                                .collect();
                            for binding in &bindings {
                                stmts.push(format!("{}.hash(state);", binding));
                            }
                            format!(
                                "Self::{}({}) => {{ {} }}",
                                v_name,
                                bindings.join(", "),
                                stmts.join(" ")
                            )
                        } else {
                            format!("Self::{} => {{ {} }}", v_name, stmts.join(" "))
                        }
                    })
                    .collect();
                format!("match self {{ {} }}", variant_hashes.join(", "))
            }
        };

        Ok(GeneratedImpl {
            trait_name: interner.intern("Hash"),
            type_name: input.name,
            methods: vec![GeneratedMethod {
                name: interner.intern("hash"),
                body: hash_body,
            }],
        })
    }

    /// Generate Default implementation
    fn generate_default(input: &DeriveInput, interner: &rv_intern::Interner) -> Result<GeneratedImpl, DeriveError> {
        let default_body = match &input.kind {
            DeriveInputKind::Struct { fields } => {
                if fields.is_empty() {
                    "Self {}".to_string()
                } else {
                    let field_defaults: Vec<String> = fields
                        .iter()
                        .enumerate()
                        .map(|(i, field)| {
                            if let Some(name) = field {
                                let name_str = interner.resolve(name);
                                format!("{}: Default::default()", name_str)
                            } else {
                                format!("{}: Default::default()", i)
                            }
                        })
                        .collect();
                    format!("Self {{ {} }}", field_defaults.join(", "))
                }
            }
            DeriveInputKind::Enum { variants } => {
                // For enums, use the first variant
                if let Some(first_variant) = variants.first() {
                    let v_name = interner.resolve(&first_variant.name);
                    if first_variant.fields.is_empty() {
                        format!("Self::{}", v_name)
                    } else {
                        let field_defaults: Vec<String> = first_variant
                            .fields
                            .iter()
                            .map(|_| "Default::default()".to_string())
                            .collect();
                        format!("Self::{}({})", v_name, field_defaults.join(", "))
                    }
                } else {
                    return Err(DeriveError::EmptyEnum);
                }
            }
        };

        Ok(GeneratedImpl {
            trait_name: interner.intern("Default"),
            type_name: input.name,
            methods: vec![GeneratedMethod {
                name: interner.intern("default"),
                body: default_body,
            }],
        })
    }
}

/// Errors that can occur during derive macro generation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeriveError {
    /// Cannot derive Default for empty enum
    EmptyEnum,
    /// Unsupported type for this derive
    UnsupportedType,
}

impl std::fmt::Display for DeriveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyEnum => write!(f, "cannot derive Default for empty enum"),
            Self::UnsupportedType => write!(f, "cannot derive for this type"),
        }
    }
}

impl std::error::Error for DeriveError {}
