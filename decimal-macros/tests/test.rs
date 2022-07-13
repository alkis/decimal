use decimal::d128;
use decimal_macros::d128 as proc_d128;
use std::str::FromStr;

#[test]
fn equivalent_to_from_str() {
    assert_eq!(proc_d128!(0.3), d128::from_str("0.3").unwrap());
}
