#[feature(plugin)]
#[plugin(decimal_macros)]
extern crate decimal_macros;

fn main() {
    let a = d128!(0.1);
    let a = d128!(0.2);
    let a = d128!(0.3);
    let res = a - b;
    let eq = res == c;
    if eq {
        println!("{} + {} = {}", a, b, res);
    } else {
        println!("{} + {} = {} (expected {})", a, b, res, c);
    }
    assert!(eq);
}