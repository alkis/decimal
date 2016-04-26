#![feature(plugin_registrar, rustc_private)]

extern crate libc;
#[doc(hidden)]
pub extern crate decimal;

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
    let mac_res = source_util::expand_stringify(cx, sp, tts);
    
    let ex = match mac_res.make_expr() {
        Some(ex) => ex,
        None => {
            cx.span_err(sp, "one argument needed");
            return DummyResult::any(sp);
        }
    };
    
    match &ex.node {
        &ExprKind::Lit(ref lit) => match &lit.node {
            &LitKind::Str(ref s, StrStyle::Cooked) => {
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
                
                let mut vec: String = "".into();
                for i in 0..16 {
                    vec.push_str(&format!("{},", num[i]));
                }
                
                let ex = syntax::parse::parse_expr_from_source_str(
                    "".into(),
                    format!("::decimal_macros::decimal::d128::from_bytes([{}])", vec),
                    cx.cfg(),
                    cx.parse_sess()
                ).unwrap();

                return MacEager::expr(ex);
            },
            _ => {}
        },
        _ => {}
    }
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
