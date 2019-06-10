#![feature(proc_macro_hygiene)]
#![feature(const_fn)]
#![allow(unused)]

extern crate decimal_macros;
extern crate decimal;

use decimal::d128;
use decimal_macros::*;

#[test]
fn basic_plugin_sanity_checks() {
    let a = d128!(0.1);
    let b = d128!(0.2);
    let c = d128!(0.3);
    let res = a + b;
    let eq = res == c;
    if eq {
        println!("{} + {} = {}", a, b, res);
    } else {
        println!("{} + {} = {} (expected {})", a, b, res, c);
    }
    assert!(eq);
    
    assert_eq!(d128!(0.1), decimal::d128::from(1) / decimal::d128::from(10));
}

#[test]
fn zero_eq_zero() {
    assert_eq!(d128!(0), decimal::d128::zero());
}

#[test]
fn create_d128_const() {
    const ZERO: decimal::d128 = { d128!(0) };
    assert_eq!(ZERO, decimal::d128::zero());
}
