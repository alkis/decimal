extern crate decimal;
extern crate proc_macro;
#[macro_use]
extern crate quote;
extern crate proc_macro2;

use proc_macro::TokenStream;
use std::str::FromStr;

#[proc_macro]
pub fn d128(input: TokenStream) -> TokenStream {
    let source = input.to_string();
    let source = source.replace(" ", "");
    let source = source.replace("_", "");

    let d = match decimal::d128::from_str(&source[..]) {
        Ok(d) => d,
        Err(e) => panic!("Unexpected decimal format for {}: {:?}", source, e),
    };
    let bytes: [u8; 16] = d.as_bytes();
    let iter = bytes.iter();
    let expanded = quote! {
        ::decimal::d128::from_raw_bytes([ #(#iter,)* ])
    };
    expanded.into()
}

#[proc_macro]
pub fn d64(input: TokenStream) -> TokenStream {
    let source = input.to_string();
    let source = source.replace(" ", "");
    let source = source.replace("_", "");
    let d = match decimal::d64::from_str(&source[..]) {
        Ok(d) => d,
        Err(e) => panic!("Unexpected decimal format for {}: {:?}", source, e),
    };
    let bytes: [u8; 8] = d.as_bytes();
    let iter = bytes.iter();
    let expanded = quote! {
        ::decimal::d64::from_raw_bytes([ #(#iter,)* ])
    };
    expanded.into()
}
