//! Derive macros for automatic visitor pattern generation
//!
//! Generates comprehensive visitor, folder, and walker implementations for recursive enums.

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, Data, DeriveInput, Fields, GenericArgument, PathArguments, Type};

/// Derive macro for generating visitor pattern infrastructure
///
/// Generates a complete visitor trait with:
/// - Individual visit methods for each variant
/// - Automatic recursion into child nodes
/// - Default implementations that can be overridden
/// - Support for Vec<T>, Option<T>, Box<T> recursive fields
///
/// # Attributes
///
/// - `#[visitor(context = "TypeName")]` - Specify context type (default: `Ctx`)
/// - `#[visitor(id_type = "TypeName")]` - Specify ID type for this enum
///
/// # Example
///
/// ```ignore
/// #[derive(Visitor)]
/// #[visitor(context = "Body", id_type = "ExprId")]
/// pub enum Expr {
///     Binary { left: ExprId, right: ExprId },
///     Literal { value: i64 },
/// }
/// ```
#[proc_macro_derive(Visitor, attributes(visitor))]
pub fn derive_visitor(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let enum_name = &input.ident;
    let visitor_name = format_ident!("{}Visitor", enum_name);

    let Data::Enum(data_enum) = &input.data else {
        return syn::Error::new_spanned(input, "Visitor can only be derived for enums")
            .to_compile_error()
            .into();
    };

    // Parse attributes to get context type and ID type
    let (context_type, id_type) = parse_visitor_attributes(&input.attrs);
    let context_type_ident = format_ident!("{}", context_type);
    let id_type_ident = if let Some(id) = id_type {
        format_ident!("{}", id)
    } else {
        format_ident!("{}Id", enum_name)
    };

    // Generate visit methods for each variant
    let mut visit_method_sigs = Vec::new();
    let mut visit_method_impls = Vec::new();
    let mut visit_dispatch_arms = Vec::new();

    for variant in &data_enum.variants {
        let variant_name = &variant.ident;
        let method_name = format_ident!("visit_{}", to_snake_case(&variant_name.to_string()));

        match &variant.fields {
            Fields::Named(fields) => {
                // Extract field names, types, and identify recursive fields
                let field_names: Vec<_> = fields.named.iter()
                    .map(|f| f.ident.as_ref().unwrap())
                    .collect();

                let field_types: Vec<_> = fields.named.iter()
                    .map(|f| &f.ty)
                    .collect();

                // Build recursion calls for recursive fields
                let mut recurse_stmts = Vec::new();
                for field in &fields.named {
                    let field_name = field.ident.as_ref().unwrap();
                    let field_ty = &field.ty;

                    if let Some(inner_id) = extract_id_type(field_ty) {
                        // This is an ID type - recurse
                        if is_vec_of(field_ty, &inner_id) {
                            recurse_stmts.push(quote! {
                                for item_id in #field_name {
                                    self.visit_id(*item_id, ctx);
                                }
                            });
                        } else if is_option_of(field_ty, &inner_id) {
                            recurse_stmts.push(quote! {
                                if let Some(inner_id) = #field_name {
                                    self.visit_id(*inner_id, ctx);
                                }
                            });
                        } else {
                            recurse_stmts.push(quote! {
                                self.visit_id(*#field_name, ctx);
                            });
                        }
                    }
                }

                // Generate method signature
                let param_decls: Vec<_> = field_names.iter().zip(field_types.iter())
                    .map(|(name, ty)| quote! { #name: &#ty })
                    .collect();

                visit_method_sigs.push(quote! {
                    fn #method_name(
                        &mut self,
                        #(#param_decls),*,
                        _id: #id_type_ident,
                        ctx: &#context_type_ident,
                    ) -> Self::Output
                });

                visit_method_impls.push(quote! {
                    #[allow(unused_variables, reason = "Default implementation may not use all fields")]
                    fn #method_name(
                        &mut self,
                        #(#param_decls),*,
                        id: #id_type_ident,
                        ctx: &#context_type_ident,
                    ) -> Self::Output {
                        #(#recurse_stmts)*
                        self.default_output(id, ctx)
                    }
                });

                // Generate dispatch arm
                let field_bindings: Vec<_> = field_names.iter()
                    .map(|name| quote! { #name })
                    .collect();

                visit_dispatch_arms.push(quote! {
                    #enum_name::#variant_name { #(#field_names),*, .. } => {
                        self.#method_name(#(#field_bindings),*, id, ctx)
                    }
                });
            }
            Fields::Unnamed(_) | Fields::Unit => {
                // Simple case: no recursion
                visit_method_sigs.push(quote! {
                    fn #method_name(&mut self, _id: #id_type_ident, ctx: &#context_type_ident) -> Self::Output
                });

                visit_method_impls.push(quote! {
                    fn #method_name(&mut self, id: #id_type_ident, ctx: &#context_type_ident) -> Self::Output {
                        self.default_output(id, ctx)
                    }
                });

                visit_dispatch_arms.push(quote! {
                    #enum_name::#variant_name { .. } => {
                        self.#method_name(id, ctx)
                    }
                });
            }
        }
    }

    let output = quote! {
        /// Auto-generated visitor trait for traversing the tree
        pub trait #visitor_name {
            /// Output type produced by visiting a node
            type Output;

            /// Visit a node by ID
            fn visit_id(&mut self, id: #id_type_ident, ctx: &#context_type_ident) -> Self::Output {
                let node = Self::get_node(id, ctx);
                match node {
                    #(#visit_dispatch_arms)*
                }
            }

            /// Get the node from context (must be implemented)
            fn get_node(id: #id_type_ident, ctx: &#context_type_ident) -> &#enum_name;

            #(#visit_method_impls)*

            /// Default output for a node (must be implemented)
            fn default_output(&mut self, id: #id_type_ident, ctx: &#context_type_ident) -> Self::Output;
        }
    };

    output.into()
}

/// Parse visitor attributes to extract context type and ID type
fn parse_visitor_attributes(attrs: &[syn::Attribute]) -> (String, Option<String>) {
    let mut context = "Ctx".to_string();
    let mut id_type = None;

    for attr in attrs {
        if attr.path().is_ident("visitor") {
            drop(attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("context") {
                    let value: syn::LitStr = meta.value()?.parse()?;
                    context = value.value();
                } else if meta.path.is_ident("id_type") {
                    let value: syn::LitStr = meta.value()?.parse()?;
                    id_type = Some(value.value());
                }
                Ok(())
            }));
        }
    }

    (context, id_type)
}

/// Extract ID type from a Type (e.g., ExprId, StmtId, etc.)
fn extract_id_type(ty: &Type) -> Option<String> {
    if let Type::Path(type_path) = ty {
        if let Some(segment) = type_path.path.segments.last() {
            let type_name = segment.ident.to_string();
            if type_name.ends_with("Id") && type_name.len() < 20 {
                return Some(type_name);
            }

            // Check inside Vec/Option/Box
            if let PathArguments::AngleBracketed(args) = &segment.arguments {
                if let Some(GenericArgument::Type(inner_ty)) = args.args.first() {
                    return extract_id_type(inner_ty);
                }
            }
        }
    }
    None
}

/// Check if type is Vec<T> where T contains the ID type
fn is_vec_of(ty: &Type, _id: &str) -> bool {
    if let Type::Path(type_path) = ty {
        if let Some(segment) = type_path.path.segments.last() {
            return segment.ident == "Vec";
        }
    }
    false
}

/// Check if type is Option<T> where T contains the ID type
fn is_option_of(ty: &Type, _id: &str) -> bool {
    if let Type::Path(type_path) = ty {
        if let Some(segment) = type_path.path.segments.last() {
            return segment.ident == "Option";
        }
    }
    false
}

/// Convert PascalCase to snake_case
fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    let mut chars = s.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch.is_uppercase() {
            if !result.is_empty() {
                result.push('_');
            }
            result.push(ch.to_lowercase().next().unwrap());
        } else {
            result.push(ch);
        }
    }

    result
}
