#![feature(plugin_registrar, rustc_private)]

extern crate libc;
extern crate decimal;

extern crate rustc_plugin;
extern crate syntax;

#[doc(hidden)]
pub use decimal;

use std::ffi::CString;

use libc::{c_char, int32_t, uint8_t, uint32_t};
use rustc_plugin::Registry;
use syntax::ext::base::{DummyResult, MacEager, ExtCtxt, MacResult};
use syntax::ext::build::AstBuilder;
use syntax::ext::source_util;
use syntax::codemap::Span;
use syntax::ast::{ExprKind, TokenTree, LitKind, StrStyle};

fn d128_lit<'cx>(cx: &'cx mut ExtCtxt, sp: Span, tts: &[TokenTree]) -> Box<MacResult + 'cx> {
    let mac_res = source_util::expand_stringify(cx, sp, tts);
    
    ec.span_fatal(sp, "test");
    
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
                
                let mut vec = Vec::with_capacity(16);
                for i in 0..16 {
                    vec.push(cx.expr_u8(lit.span, 0/*num[i]*/));
                }
                let arr = cx.expr_vec(sp, vec);
                
                return MacEager::expr(arr);
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

fn from_str(s: &str) -> Result<[uint8_t; 16], &'static str> {
    let cstr = match CString::new(s) {
        Err(..)  => return Err("not a valid d128 number"),
        Ok(cstr) => cstr,
    };
    let mut ctx = default_context();
    let mut res: [uint8_t; 16];
    unsafe {
        res = std::mem::uninitialized();
        decQuadFromString(&mut res, cstr.as_ptr(), &mut ctx);
    }
    if ctx.status & 0x00000001 != 0 { // CONVERSION_SYNTAX
        Err("not a valid d128 number")
    } else if ctx.status & 0x00000200 != 0 { // OVERFLOW
        Err("too large for a d128 number")
    } else if ctx.status & 0x00002000 != 0 { // UNDERFLOW
        Err("too small for a d128 number")
    } else if ctx.status != 0 {
        Err("not a valid d128 number")
    } else {
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    
}
