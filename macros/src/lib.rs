use core::panic;
use std::iter::zip;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{
    parse_macro_input, Data, DeriveInput, Fields, GenericArgument, Ident, PathArguments, Type,
};

fn process_vec_element(element_type: &Type) -> Option<proc_macro2::TokenStream> {
    if let Type::Path(path) = element_type {
        if let Some(last_segment) = path.path.segments.last() {
            if last_segment.ident == "Value" {
                return Option::Some(quote!(resolve_types_value(
                    element, function, globals, lexer
                )));
            } else if last_segment.ident == "Type" {
                return Option::Some(quote!(resolve_actual_type(&element, globals, lexer)));
            } else if last_segment.ident == "Phi" {
                return Option::Some(quote!(resolve_types_phi(element, function, globals, lexer)));
            }
        }
    };
    Option::None
}

fn process_field(field_name: &Ident, field_type: &Type) -> proc_macro2::TokenStream {
    if let Type::Path(path) = field_type {
        if let Some(last_segment) = path.path.segments.last() {
            if last_segment.ident == "Value" {
                return quote!(resolve_types_value(#field_name, function, globals, lexer)?);
            } else if last_segment.ident == "Type" {
                return quote!(resolve_actual_type(&#field_name, globals, lexer)?);
            } else if last_segment.ident == "Scope" {
                return quote!(resolve_types_scope(&#field_name, function, globals, lexer)?);
            } else if last_segment.ident == "Fields" {
                return quote!(resolve_actual_fields(#field_name, globals, lexer)?);
            } else if last_segment.ident == "Vec" {
                if let PathArguments::AngleBracketed(args) = &last_segment.arguments {
                    if args.args.len() == 1 {
                        if let GenericArgument::Type(arg_type) = &args.args[0] {
                            if let Some(process_element) = process_vec_element(arg_type) {
                                return quote!(#field_name.into_iter().map(|element| #process_element).collect::<Result<Vec<_>, String>>()?);
                            }
                        }
                    }
                }
            }
        }
    };
    quote!(#field_name)
}

#[proc_macro_derive(ResolveTypes)]
pub fn derive_resolve_types(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let type_name = input.ident;

    let variants = if let Data::Enum(data) = input.data {
        data.variants
    } else {
        panic!("this macro only works for enums");
    };

    let match_arms: Vec<_> = variants.into_iter().map(|variant| {
        let variant_name = variant.ident;

        match variant.fields {
            Fields::Named(_) => panic!("named fields aren't supported yet"),
            Fields::Unnamed(fields) => {
                let pattern_fields: Vec<_> = fields
                    .unnamed
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Ident::new(&format!("field_{i}"), Span::call_site()))
                    .collect();

                let processed_fields: Vec<_> = zip(pattern_fields.iter(), fields.unnamed)
                    .map(|(field_name, field)| {
                        process_field(field_name, &field.ty)
                    })
                    .collect();

                quote! {
                    #type_name::#variant_name(#(#pattern_fields),*) => #type_name::#variant_name(#(#processed_fields),*)
                }
            }
            Fields::Unit => {
                quote! {
                    #type_name::#variant_name => #type_name::#variant_name
                }
            }
        }
    }).collect();

    let result = quote! {
        impl ResolveTypes for #type_name {
            fn resolve_types(self, function: &mut Function, globals: &mut Globals, lexer: &Lexer) -> Result<Self, String> {
                Result::Ok(match self {
                    #(#match_arms),*
                })
            }
        }
    };
    result.into()
}
