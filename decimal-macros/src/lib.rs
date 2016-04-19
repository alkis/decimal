#![feature(plugin_registrar, rustc_private)]

extern crate rustc_plugin;
extern crate syntax;
extern crate libc;

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
                    vec.push(cx.expr_u8(lit.span, num[i]));
                }
                return MacEager::expr(cx.expr_vec(sp, vec));
            },
            _ => {}
        },
        _ => {}
    }
    cx.span_err(sp, "not a valid number");
    DummyResult::any(sp)
}

/*
fn expr_to_string(cx: &mut ExtCtxt, expr: P<Expr>, err_msg: &'static str) -> Option<String> {
    let mut s = String::new();
    match expr_append(cx, &mut s, expr, err_msg) {
        Ok(())  => Some(s),
        Err(()) => None,
    }
}

fn expr_append(cx: &mut ExtCtxt, s: &mut String, expr: P<Expr>, err_msg: &'static str) -> Result<(), ()> {
    match expr.clone().node {
        ExprKind::Lit(lit) => {
            match lit.node { // Ignore suffixes
                LitKind::Int(i, _)          => s.push_str(&i.to_string()),
                LitKind::Float(s, _)        => s.push_str(&*s),
                LitKind::FloatUnsuffixed(s) => s.push_str(&*s),
                _ => {}
            }
        },
        _ => {
            cx.span_err(expr.clone().span, &format!("expr: {:?}", expr.clone().node));
            cx.span_err(expr.span, err_msg);
            None
        },
    }
}*/

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("dmacros_d128", d128_lit)
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
struct Context {
    digits: int32_t,
    emax: int32_t,
    emin: int32_t,
    rounding: Rounding,
    traps: uint32_t,
    status: uint32_t,
    clamp: uint8_t,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
#[allow(dead_code)]
enum Rounding {
    Ceiling = 0,
    Up,
    HalfUp,
    /// Round to nearest; if equidistant, round so that the final digit is even.
    /// This is the only rounding mode supported.
    HalfEven,
    HalfDown,
    Down,
    Floor,
    ZeroOrFiveUp,
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
        println!("ctx.status: {:#x}, ctx: {:?}", ctx.status, ctx);
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

fn default_context() -> Context {
    unsafe {
        let mut res: Context = std::mem::uninitialized();
        *decContextDefault(&mut res, 128)
    }
}

extern "C" {
    fn decContextDefault(ctx: *mut Context, kind: uint32_t) -> *mut Context;
    fn decQuadFromString(res: *mut [uint8_t; 16], s: *const c_char, ctx: *mut Context) -> *mut [uint8_t; 16];
}
