#![feature(plugin_registrar, rustc_private)]

extern crate libc;
extern crate decimal;

extern crate rustc_plugin;
extern crate syntax;

use rustc_plugin::Registry;
use syntax::ext::base::{DummyResult, MacEager, ExtCtxt, MacResult};
use syntax::ext::build::AstBuilder;
use syntax::ext::source_util;
use syntax::codemap::Span;
use syntax::ast::{ExprKind, LitKind, StrStyle};
use syntax::tokenstream::TokenTree;

use decimal::d128;

fn d128_lit<'cx>(cx: &'cx mut ExtCtxt, sp: Span, tts: &[TokenTree]) -> Box<MacResult + 'cx> {
    // Turn input into a string literal
    // e.g. d128!(0.1) -> "0.1", d128!(NaN) -> "NaN"
    let mac_res = source_util::expand_stringify(cx, sp, tts);
    
    let ex = match mac_res.make_expr() {
        Some(ex) => ex,
        None => {
            // I don't know when this occurs
            cx.span_err(sp, "one argument needed");
            return DummyResult::any(sp);
        }
    };
    
    match &ex.node {
        &ExprKind::Lit(ref lit) => match &lit.node {
            &LitKind::Str(ref s, StrStyle::Cooked) => {
                // Check for empty argument
                if s.as_str().len() == 0 {
                    cx.span_err(sp, "one argument needed");
                    return DummyResult::any(sp);
                }
                let num = match from_str(s.as_str().as_ref()) {
                    Ok(num) => num,
                    Err(s) => {
                        cx.span_err(lit.span, s);
                        return DummyResult::any(sp);
                    }
                };
                let num = unsafe { ::std::mem::transmute::<d128, [u8; 16]>(num) };
                
                // Create array literal
                let mut vec = Vec::new();
                for i in 0..16 {
                    vec.push(cx.expr_u8(lit.span, num[i]));
                }
                let vec = cx.expr_vec(lit.span, vec);
                let ids = vec![cx.ident_of("decimal"), cx.ident_of("d128"), cx.ident_of("from_raw_bytes")];
                let ex = cx.expr_call_global(lit.span, ids, vec![vec]);
                
                return MacEager::expr(ex);
            },
            _ => {}
        },
        _ => {}
    }
    // This should never happen.
    cx.span_err(sp, "not a valid d128 number");
    DummyResult::any(sp)
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("d128", d128_lit)
}

fn from_str(s: &str) -> Result<d128, &'static str> {
    use std::str::FromStr;
    d128::set_status(decimal::Status::empty());
    let no_spaces = s.replace(" ", "");
    let res = d128::from_str(&no_spaces);
    
    let status = d128::get_status();
    if status.contains(decimal::Status::CONVERSION_SYNTAX) {
        println!("{} {:?}", s, res);
        Err("not a valid d128 number (CONVERSION_SYNTAX)")
    } else if status.contains(decimal::Status::OVERFLOW) {
        Err("too large for a d128 number (OVERFLOW)")
    } else if status.contains(decimal::Status::UNDERFLOW) {
        Err("too small for a d128 number (UNDERFLOW)")
    } else if !status.is_empty() {
        Err("not a valid d128 number (is_empty)")
    } else {
        Ok(res.unwrap())
    }
}
