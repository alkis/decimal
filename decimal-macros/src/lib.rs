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
use syntax::ast::{ExprKind, TokenTree, LitKind, StrStyle};

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
                //cx.span_warn(lit.span, &format!("Parsing \"{}\"...", s));
                // Check for empty argument
                if (*s).len() == 0 {
                    cx.span_err(sp, "one argument needed");
                    return DummyResult::any(sp);
                }
                let num = match from_str(&*s) {
                    Ok(num) => num,
                    Err(s) => {
                        cx.span_err(lit.span, s);
                        return DummyResult::any(sp);
                    }
                }; 
                let num = unsafe { ::std::mem::transmute::<d128, [u8; 16]>(num) };
                
                // cx.span_warn(lit.span, &format!("{} -> {:?}", s, num));
                
                // Create array literal
                let mut vec = Vec::new();
                for i in 0..16 {
                    vec.push(cx.expr_u8(lit.span, num[i]));
                }
                let vec = cx.expr_vec(lit.span, vec);
                let ids = vec![cx.ident_of("decimal"), cx.ident_of("d128"), cx.ident_of("from_bytes")];
                let ex = cx.expr_call_global(lit.span, ids, vec![vec]); // Call ::decimal::d128::from_bytes with array literal
                
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
    let res = d128::from_str(s);
    
    let status = d128::get_status();
    if status.contains(decimal::CONVERSION_SYNTAX) {
        Err("not a valid d128 number")
    } else if status.contains(decimal::OVERFLOW) {
        Err("too large for a d128 number")
    } else if status.contains(decimal::UNDERFLOW) {
        Err("too small for a d128 number")
    } else if !status.is_empty() {
        Err("not a valid d128 number")
    } else {
        Ok(res.unwrap())
    }
}
