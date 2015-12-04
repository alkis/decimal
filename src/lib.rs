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

pub use context::rounding;
pub use dec128::d128;
