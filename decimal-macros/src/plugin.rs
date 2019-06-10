//#![feature(plugin_registrar, rustc_private, const_let, const_fn)]
#![crate_name = "decimal_macros"]
#![crate_type = "dylib"]
#![feature(plugin_registrar)]
#![feature(rustc_private)]

extern crate libc;
extern crate decimal;

extern crate rustc_plugin;
extern crate syntax;

use rustc_plugin::Registry;
use syntax::ext::base::{DummyResult, MacEager, ExtCtxt, MacResult};
#[allow(unused_imports)]
use syntax::ext::build::AstBuilder;
use syntax::ext::source_util;
use syntax::source_map::Span; // changes after nightly-2018-08-06
//use syntax::codemap::Span;
use syntax::ast::{ExprKind, LitKind, StrStyle};
use syntax::tokenstream::TokenTree;

use decimal::{d128, d64};

// pub use self::d128_lit::*;
// pub use self::d64_lit::*;

/*
 * just putting this here for posterity
 *

#[macro_export]
/// A macro to construct d128 literals.
///
/// # Examples:
/// ```
/// # #[macro_use]
/// # extern crate decimal;
/// # use decimal::d128;
/// # use std::str::FromStr;
/// # fn main() {
/// assert!(d128!(NaN).is_nan());
/// assert!(d128!(0).is_zero());
/// assert!(d128!(-0.1).is_negative());
/// assert_eq!(d128!(1.2345), d128::from_str("1.2345").unwrap());
/// // underscore separators work, too
/// assert_eq!(d128!(1_000_000), d128::from_str("1000000").unwrap());
/// # }
/// ```
macro_rules! d128 {
    ($lit:expr) => {{
        use std::str::FromStr;
        let lit = stringify!($lit);
        let clean: String = lit.replace("_", "");
        $crate::d128::from_str(&clean).expect("Invalid decimal float literal")
    }}
}

#[macro_export]
/// A macro to construct d64 literals.
///
/// # Examples:
/// ```
/// # #[macro_use]
/// # extern crate decimal;
/// # use decimal::d64;
/// # use std::str::FromStr;
/// # fn main() {
/// assert!(d64!(NaN).is_nan());
/// assert!(d64!(0).is_zero());
/// assert!(d64!(-0.1).is_negative());
/// assert_eq!(d64!(1.2345), d64::from_str("1.2345").unwrap());
/// // underscore separators work, too
/// assert_eq!(d64!(1_000_000), d64::from_str("1000000").unwrap());
/// # }
/// ```
macro_rules! d64 {
    ($lit:expr) => {{
        use std::str::FromStr;
        $crate::d64::from_str(stringify!($lit)).expect("Invalid decimal float literal")
    }}
}
*/

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("d64", self::d64_lit::d64_lit);
    reg.register_macro("d128", self::d128_lit::d128_lit);
}

mod d128_lit {
    use super::*;

    pub(crate) fn d128_lit<'cx>(cx: &'cx mut ExtCtxt, sp: Span, tts: &[TokenTree]) -> Box<MacResult + 'cx> {
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

                    // remove underscore separators
                    let clean: String = s.as_str().replace("_", "");

                    let num = match d128_from_str(&clean) {
                        Ok(num) => num,
                        Err(s) => {
                            cx.span_err(lit.span, s);
                            return DummyResult::any(sp);
                        }
                    };

                    let num = num.as_bytes();

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

    fn d128_from_str(s: &str) -> Result<d128, &'static str> {
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

}

mod d64_lit {
    use super::*;

    pub(crate) fn d64_lit<'cx>(cx: &'cx mut ExtCtxt, sp: Span, tts: &[TokenTree]) -> Box<MacResult + 'cx> {
        // Turn input into a string literal
        // e.g. d64!(0.1) -> "0.1", d64!(NaN) -> "NaN"
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

                    // remove underscore separators
                    let clean: String = s.as_str().replace("_", "");

                    let num = match d64_from_str(&clean) {
                        Ok(num) => num,
                        Err(s) => {
                            cx.span_err(lit.span, s);
                            return DummyResult::any(sp);
                        }
                    };

                    let num = num.as_bytes();

                    // Create array literal
                    let mut vec = Vec::new();
                    for i in 0..8 {
                        vec.push(cx.expr_u8(lit.span, num[i]));
                    }
                    let vec = cx.expr_vec(lit.span, vec);
                    let ids = vec![cx.ident_of("decimal"), cx.ident_of("d64"), cx.ident_of("from_raw_bytes")];
                    let ex = cx.expr_call_global(lit.span, ids, vec![vec]);

                    return MacEager::expr(ex);
                },
                _ => {}
            },
            _ => {}
        }
        // This should never happen.
        cx.span_err(sp, "not a valid d64 number");
        DummyResult::any(sp)
    }

    fn d64_from_str(s: &str) -> Result<d64, &'static str> {
        use std::str::FromStr;
        d64::set_status(decimal::Status::empty());
        let no_spaces = s.replace(" ", "");
        let res = d64::from_str(&no_spaces);

        let status = d64::get_status();
        if status.contains(decimal::Status::CONVERSION_SYNTAX) {
            println!("{} {:?}", s, res);
            Err("not a valid d64 number (CONVERSION_SYNTAX)")
        } else if status.contains(decimal::Status::OVERFLOW) {
            Err("too large for a d64 number (OVERFLOW)")
        } else if status.contains(decimal::Status::UNDERFLOW) {
            Err("too small for a d64 number (UNDERFLOW)")
        } else if !status.is_empty() {
            Err("not a valid d64 number (is_empty)")
        } else {
            Ok(res.unwrap())
        }
    }
}
