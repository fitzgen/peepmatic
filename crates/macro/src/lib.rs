extern crate proc_macro;

use self::proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::DeriveInput;
use syn::Error;
use syn::{parse_macro_input, parse_quote, GenericParam, Generics, Ident, Result};

#[proc_macro_derive(Span)]
pub fn derive_span(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let ty = &input.ident;

    let body = match input.data {
        syn::Data::Struct(_) => quote! { self.span },
        syn::Data::Enum(e) => {
            let variants = e.variants.iter().map(|v| match v.fields {
                syn::Fields::Unnamed(ref fields) if fields.unnamed.len() == 1 => {
                    let variant = &v.ident;
                    quote! { #ty::#variant(x) => x.span(), }
                }
                _ => panic!(
                    "derive(Span) on enums only supports variants with a single, unnamed field"
                ),
            });
            quote! {
                match self {
                    #( #variants )*
                }
            }
        }
        syn::Data::Union(_) => panic!("derive(Span) can only be used with structs and unions"),
    };

    let generics = add_span_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let expanded = quote! {
        impl #impl_generics Span for #ty #ty_generics #where_clause {
            #[inline]
            fn span(&self) -> wast::Span {
                #body
            }
        }
    };

    TokenStream::from(expanded)
}

// Add a bound `T: Span` to every type parameter `T`.
fn add_span_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(Span));
        }
    }
    generics
}

#[proc_macro_attribute]
pub fn peepmatic(_attr: TokenStream, input: TokenStream) -> TokenStream {
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
                opts: syn::parse(peepmatic_attrs(&mut variant.attrs))?,
                syn: variant,
            })
        })
        .collect()
}

struct OperatorVariant {
    syn: syn::Variant,
    opts: OperatorVariantOpts,
}

#[derive(Default)]
struct OperatorVariantOpts {
    immediates_paren: syn::token::Paren,
    immediates: Vec<syn::Ident>,
    params_paren: syn::token::Paren,
    params: Vec<syn::Ident>,
    result: Option<syn::Ident>,
}

impl Parse for OperatorVariantOpts {
    fn parse(input: ParseStream) -> Result<Self> {
        enum Attr {
            Immediates(syn::token::Paren, Vec<syn::Ident>),
            Params(syn::token::Paren, Vec<syn::Ident>),
            Result(syn::Ident),
        }

        let attrs = Punctuated::<_, syn::token::Comma>::parse_terminated(input)?;
        let mut ret = OperatorVariantOpts::default();
        for attr in attrs {
            match attr {
                Attr::Immediates(paren, imms) => {
                    ret.immediates_paren = paren;
                    ret.immediates = imms;
                }
                Attr::Params(paren, ps) => {
                    ret.params_paren = paren;
                    ret.params = ps;
                }
                Attr::Result(r) => ret.result = Some(r),
            }
        }

        if ret.result.is_none() {
            return Err(Error::new(
                input.span(),
                "missing `#[peepmatic(result(..))]`",
            ));
        }

        return Ok(ret);

        impl Parse for Attr {
            fn parse(input: ParseStream) -> Result<Self> {
                let attr: Ident = input.parse()?;
                if attr == "immediates" {
                    let inner;
                    let paren = syn::parenthesized!(inner in input);
                    let imms = Punctuated::<_, syn::token::Comma>::parse_terminated(&inner)?;
                    return Ok(Attr::Immediates(paren, imms.into_iter().collect()));
                }
                if attr == "params" {
                    let inner;
                    let paren = syn::parenthesized!(inner in input);
                    let params = Punctuated::<_, syn::token::Comma>::parse_terminated(&inner)?;
                    return Ok(Attr::Params(paren, params.into_iter().collect()));
                }
                if attr == "result" {
                    let inner;
                    syn::parenthesized!(inner in input);
                    return Ok(Attr::Result(syn::Ident::parse(&inner)?));
                }
                return Err(Error::new(attr.span(), "unexpected attribute"));
            }
        }
    }
}

fn peepmatic_attrs(attrs: &mut Vec<syn::Attribute>) -> TokenStream {
    let mut ret = proc_macro2::TokenStream::new();
    let ident = syn::Path::from(syn::Ident::new("peepmatic", Span::call_site()));
    for i in (0..attrs.len()).rev() {
        if attrs[i].path != ident {
            continue;
        }
        let attr = attrs.remove(i);
        let group = match attr.tokens.into_iter().next().unwrap() {
            proc_macro2::TokenTree::Group(g) => g,
            _ => panic!("#[peepmatic(...)] expected"),
        };
        ret.extend(group.stream());
        ret.extend(quote! { , });
    }
    return ret.into();
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

        let result_ty = v.opts.result.as_ref().unwrap();
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
