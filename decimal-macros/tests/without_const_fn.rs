#![feature(plugin)]
#![plugin(decimal_macros)]
extern crate decimal;

use decimal::d128;
use std::str::FromStr;

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
fn it_parses_a_negative_number() {
    assert_eq!(d128!(-1), d128::from_str("-1").unwrap());
    assert_eq!(d128!(-0.1), d128::from_str("-0.1").unwrap());
}

#[test]
fn it_does_not_parse_a_negative_number_but_we_check_something_else() {
    assert_eq!(-d128!(1), d128::from_str("-1").unwrap());
    assert_eq!(-d128!(0.1), d128::from_str("-0.1").unwrap());
}

#[test]
fn it_parses_nan() {
    assert!(d128!(NaN).is_nan());
}


