#[macro_use]
extern crate bitflags;
extern crate libc;
#[macro_use]
extern crate quick_error;

#[macro_export]
macro_rules! d128 {
    ($lit:expr) => {{
        use std::str::FromStr;
        d128::from_str(stringify!($lit)).expect("Invalid decimal float literal")
    }}
}

mod context;
mod dec128;
mod error;

pub use context::Context;
pub use dec128::d128;

#[repr(C)]
#[derive(Debug, PartialEq)]
pub enum Rounding {
    Ceiling = 0,
    Up,
    HalfUp,
    HalfEven,
    HalfDown,
    Down,
    Floor,
    ZeroOrFiveUp,
}

#[repr(C)]
#[derive(Debug, PartialEq)]
#[allow(dead_code)]
pub enum Class {
    Snan = 0,
    Qnan,
    NegInf,
    NegNormal,
    NegSubnormal,
    NegZero,
    PosZero,
    PosSubnormal,
    PosNormal,
    PosInf,
}

bitflags! {
    flags Status: u32 {
        const CONVERSION_SYNTAX    = 0x00000001,
        const DIVISION_BY_ZERO     = 0x00000002,
        const DIVISION_IMPOSSIBLE  = 0x00000004,
        const DIVISION_UNDEFINED   = 0x00000008,
        const INSUFFICIENT_STORAGE = 0x00000010,
        const INEXACT              = 0x00000020,
        const INVALID_CONTEXT      = 0x00000040,
        const INVALID_OPERATION    = 0x00000080,
        const LOST_DIGITS          = 0x00000100,
        const OVERFLOW             = 0x00000200,
        const CLAMPED              = 0x00000400,
        const ROUNDED              = 0x00000800,
        const SUBNORMAL            = 0x00001000,
        const UNDERFLOW            = 0x00002000,
    }
}
