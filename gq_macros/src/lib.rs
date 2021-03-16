use core::panic;

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{ToTokens, quote};
use syn::{Attribute, DeriveInput, parse_macro_input};

use heck::{ShoutySnekCase, CamelCase};

fn parse_doc_string(attrs: &[Attribute]) -> Option<String> {
    attrs.iter()
        .filter_map(|attr| {
            if attr.path.get_ident()?.to_string() != "doc" { return None }

            let meta = match attr.parse_meta().unwrap() {
                syn::Meta::NameValue(meta) => meta,
                _ => panic!("bad doc attr")
            };

            let mut doc = match meta.lit {
                syn::Lit::Str(s) => s.value(),
                _ => panic!("bad doc attr")
            };

            if doc.starts_with(" ") { doc.remove(0); };

            Some(doc)
        }).fold(None, |acc, el| {
            let mut acc = acc.unwrap_or(String::new());

            acc.push_str(&el);
            
            Some(acc)
        })
}

fn option_literal<T: ToTokens>(option: Option<T>) -> TokenStream2 {
    match option {
        Some(a) => quote!( Some(#a) ),
        None => quote!( None )
    }
}

#[proc_macro_derive(EnumValue)]
pub fn derive_enum_value(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree
    let input = parse_macro_input!(input as DeriveInput);

    let ident = &input.ident;
    let gql_name = input.ident.to_string().to_camel_case();
    let description = option_literal(parse_doc_string(&input.attrs));

    let data = match input.data {
        syn::Data::Enum(data) => data ,
        _ => panic!("")
    };

    let variant_idents: Vec<_> = data.variants.iter().map(|var| var.ident.clone()).collect();
    let variant_names: Vec<_> = data.variants.iter().map(|var| var.ident.to_string().TO_SHOUTY_SNEK_CASE()).collect();
    let variant_descriptions = data.variants.iter().map(|var| option_literal(parse_doc_string(&var.attrs)));

    // Build the output, possibly using quasi-quotation
    let expanded = quote! {
        impl EnumValue for #ident {
            const NAME: &'static str = #gql_name;

            const VALUES: &'static [Self] = &[
                #(
                    Self::#variant_idents,
                )*
            ];

            const DESCRIPTION: Option<&'static str> = #description;

            fn value(&self) -> &str {
                match self {
                    #(
                        Self::#variant_idents => #variant_names,
                    )*
                }
            }

            fn description(&self) -> Option<&'static str> {
                match self {
                    #(
                        Self::#variant_idents => #variant_descriptions,
                    )*
                }
            }

            fn from_value(value: &str) -> Option<Self> {
                match value {
                    #(
                        #variant_names => Some(Self::#variant_idents),
                    )*
                    _ => None
                }
            }
        }
    };

    // Hand the output tokens back to the compiler
    TokenStream::from(expanded)
}
