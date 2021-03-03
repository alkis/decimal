# decimal

[![Travis](https://img.shields.io/travis/alkis/decimal.svg)](https://travis-ci.org/alkis/decimal)
![Downloads](https://img.shields.io/crates/d/decimal.svg)
[![Crates.io](https://img.shields.io/crates/v/decimal.svg)](https://crates.io/crates/decimal)
![Apache license](https://img.shields.io/crates/l/decimal.svg)

Decimal Floating Point arithmetic for rust based on the [decNumber
library](http://speleotrove.com/decimal/decnumber.html).

The library provides d128 which is a [128-bit decimal floating
point](https://en.wikipedia.org/wiki/Decimal128_floating-point_format) number.
You can use it as other primitive numbers in Rust. All operators are overloaded
to allow ergonomic use of this type.

To emulate literals a macro is used `d128!`.

[Documentation](https://docs.rs/decimal)

# Example

```rust
let x = d128!(1.234);
let y = d128!(1.111);
let z = d128!(2.345);
assert_eq(x + y, z);
```

# Running the [decTest](http://speleotrove.com/decimal/dectest.html) test suite

```bash
$ cargo build
$ ./target/debug/run-test decTest/decQuad.decTest
```
# (De)serializing using serde

`d128` supports (de)serialization using serde by default (feature `serde`). d128 is serialized from and to string:

```rust
    assert_eq!(d128!(5.4321), serde_json::from_str("\"5.4321\"").unwrap());
    assert_eq!("\"1.2345\"".to_string(), serde_json::to_string(&d128!(1.2345)).unwrap());
```

If you want to deserialize from numbers, e.g. in json, enable the features `serde` and `serde_lossy`.
This will make serde _de_serialize integer and floating-point numbers as well.

_Note_: Due to the way serde is designed, using `serde_lossy` to deserialize fractions such as `0.3` can incur in
*loss of precision*, as the number is deserialized to `f64` first before being converted to `d128`. This is why
d128 are only ever serialized to Strings. Still, it can make sense to enable `serde_lossy` for an initial import of 
data that only exists as floating point json; which is from then on treated as d128.
