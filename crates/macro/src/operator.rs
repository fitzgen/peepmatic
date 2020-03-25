//! Implementation of the `#[peepmatic]` macro for the `Operator` AST node.

use crate::proc_macro::TokenStream;
use crate::PeepmaticOpts;
use quote::quote;
use syn::DeriveInput;
use syn::Error;
use syn::{parse_macro_input, Result};

pub fn peepmatic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    assert_eq!(input.ident.to_string(), "Operator");

    let variants = match get_enum_variants(&input) {
        Ok(v) => v,
        Err(e) => return e.to_compile_error().into(),
    };

    let operator = create_enum_operator(&input.attrs, &variants);
    let arity = match create_arity(&variants) {
        Ok(a) => a,
        Err(e) => return e.to_compile_error().into(),
    };
    let type_methods = create_type_methods(&variants);

    let expanded = quote! {
        #operator

        impl Operator {
            #arity
            #type_methods
        }
    };

    // eprintln!("{}", expanded);
    TokenStream::from(expanded)
}

fn get_enum_variants(input: &DeriveInput) -> Result<Vec<OperatorVariant>> {
    let en = match &input.data {
        syn::Data::Enum(en) => en,
        syn::Data::Struct(_) => {
            panic!("can only put #[peepmatic] on an enum; found it on a struct")
        }
        syn::Data::Union(_) => panic!("can only put #[peepmatic] on an enum; found it on a union"),
    };
    en.variants
        .iter()
        .cloned()
        .map(|mut variant| {
            Ok(OperatorVariant {
                opts: PeepmaticOpts::from_attrs(&mut variant.attrs)?,
                syn: variant,
            })
        })
        .collect()
}

struct OperatorVariant {
    syn: syn::Variant,
    opts: PeepmaticOpts,
}

fn create_enum_operator(
    attrs: &[syn::Attribute],
    variants: &[OperatorVariant],
) -> impl quote::ToTokens {
    let variants = variants.iter().map(|v| &v.syn);
    quote! {
        #( #attrs )*
        pub enum Operator {
            #( #variants ),*
        }
    }
}

fn create_arity(variants: &[OperatorVariant]) -> Result<impl quote::ToTokens> {
    let mut imm_arities = vec![];
    let mut params_arities = vec![];

    for v in variants {
        let variant = &v.syn.ident;

        let imm_arity = v.opts.immediates.len();
        if imm_arity > std::u8::MAX as usize {
            return Err(Error::new(
                v.opts.immediates_paren.span,
                "cannot have more than u8::MAX immediates",
            ));
        }
        let imm_arity = imm_arity as u8;

        imm_arities.push(quote! {
            Operator::#variant => #imm_arity,
        });

        let params_arity = v.opts.params.len();
        if params_arity > std::u8::MAX as usize {
            return Err(Error::new(
                v.opts.params_paren.span,
                "cannot have more than u8::MAX params",
            ));
        }
        let params_arity = params_arity as u8;

        params_arities.push(quote! {
            Operator::#variant => #params_arity,
        });
    }

    Ok(quote! {
        /// Get the number of immediates that this operator has.
        pub fn immediates_arity(&self) -> u8 {
            match *self {
                #( #imm_arities )*
            }
        }

        /// Get the number of parameters that this operator takes.
        pub fn params_arity(&self) -> u8 {
            match *self {
                #( #params_arities )*
            }
        }
    })
}

fn create_type_methods(variants: &[OperatorVariant]) -> impl quote::ToTokens {
    let mut result_types = vec![];
    let mut imm_types = vec![];
    let mut param_types = vec![];

    for v in variants {
        let variant = &v.syn.ident;

        let result_ty = v.opts.result.as_ref().unwrap_or_else(|| {
            panic!(
                "must define #[peepmatic(result(..))] on operator `{}`",
                variant
            )
        });
        result_types.push(quote! {
            Operator::#variant => {
                context.#result_ty(span)
            }
        });

        let imm_tys = match &v.opts.immediates[..] {
            [] => quote! {},
            [ty, rest @ ..] => {
                let rest = rest.iter().map(|ty| {
                    quote! { .chain(::std::iter::once(context.#ty(span))) }
                });
                quote! {
                    types.extend(::std::iter::once(context.#ty(span))#( #rest )*);
                }
            }
        };
        imm_types.push(quote! {
            Operator::#variant => {
                #imm_tys
            }
        });

        let param_tys = match &v.opts.params[..] {
            [] => quote! {},
            [ty, rest @ ..] => {
                let rest = rest.iter().map(|ty| {
                    quote! { .chain(::std::iter::once(context.#ty(span))) }
                });
                quote! {
                    types.extend(::std::iter::once(context.#ty(span))#( #rest )*);
                }
            }
        };
        param_types.push(quote! {
            Operator::#variant => {
                #param_tys
            }
        });
    }

    quote! {
        pub(crate) fn result_type<'a>(
            &self,
            context: &mut crate::verify::TypingContext<'a>,
            span: wast::Span,
        ) -> crate::verify::TypeVar<'a> {
            match *self {
                #( #result_types )*
            }
        }

        pub(crate) fn immediate_types<'a>(
            &self,
            context: &mut crate::verify::TypingContext<'a>,
            span: wast::Span,
            types: &mut impl Extend<crate::verify::TypeVar<'a>>,
        ) {
            match *self {
                #( #imm_types )*
            }
        }

        pub(crate) fn param_types<'a>(
            &self,
            context: &mut crate::verify::TypingContext<'a>,
            span: wast::Span,
            types: &mut impl Extend<crate::verify::TypeVar<'a>>,
        ) {
            match *self {
                #( #param_types )*
            }
        }
    }
}
