#![feature(plugin, const_fn)]
#![plugin(decimal_macros)]
extern crate decimal;

use decimal::d128;

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
    
    assert_eq!(d128!(0.1), d128::from(1) / d128::from(10));
}

#[test]
fn zero_eq_zero() {
    assert_eq!(d128!(0), d128::zero());
}

#[test]
fn create_d128_const() {
    const ZERO: d128 = d128!(0);
    assert_eq!(ZERO, d128::zero());
}

