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
