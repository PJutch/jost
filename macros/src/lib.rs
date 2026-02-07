use core::panic;
use std::iter::zip;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Fields, Ident, Type};

fn is_value(type_: &Type) -> bool {
    quote!(#type_).to_string() == "Value"
}

fn is_type(type_: &Type) -> bool {
    quote!(#type_).to_string() == "Type"
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
                        if is_value(&field.ty) {
                            quote! {resolve_types_value(#field_name, function, globals, lexer)?}
                        } else if is_type(&field.ty) {
                            quote! {resolve_actual_type(&#field_name, globals, lexer)?}
                        } else {
                            quote! {#field_name}
                        }
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
