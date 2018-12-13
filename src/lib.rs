#![feature(const_fn)]
#![cfg_attr(test, feature(test))]

#[macro_use]
extern crate bitflags;
extern crate libc;
#[cfg(feature = "ord_subset")]
extern crate ord_subset;
#[cfg(feature = "rustc-serialize")]
extern crate rustc_serialize;
#[cfg(feature = "serde")]
extern crate serde;
#[cfg(feature = "serde")]
#[cfg(test)]
extern crate serde_json;
#[cfg(test)]
extern crate rand;
#[cfg(test)]
extern crate test;
#[cfg(feature = "faster")]
extern crate faster;
#[cfg(feature = "slog")]
extern crate slog;
#[cfg(test)]
#[macro_use]
extern crate approx;

mod context;
mod dec128;
mod dec64;

pub use crate::dec128::d128;
pub use crate::dec64::d64;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Rounding {
    Ceiling = 0,
    Up,
    HalfUp,
    /// Round to nearest; if equidistant, round so that the final digit is even.
    /// This is the only rounding mode supported.
    HalfEven,
    HalfDown,
    Down,
    Floor,
    ZeroOrFiveUp,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
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
    /// The status of the floating point context. Instead of faulting after every operation errors
    /// are added to this status. User code can check and/or clear the status fully or partially at
    /// specific points to check the validity of the computation. Each thread gets its own status.
    /// The status is initially empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![feature(proc_macro_hygiene)]
    /// # extern crate decimal_macros;
    /// # extern crate decimal;
    /// # use decimal_macros::*;
    /// # use decimal::d128;
    /// # use decimal::Status;
    /// # fn main() {
    /// assert_eq!(d128::get_status(), Status::empty());
    /// let _ = d128!(1) / &d128!(0);
    /// assert!(d128::get_status().contains(decimal::Status::DIVISION_BY_ZERO));
    /// let _ = d128!(0) / &d128!(0);
    /// assert!(d128::get_status().contains(decimal::Status::DIVISION_UNDEFINED));
    /// // The previous status flag was not cleared!
    /// assert!(d128::get_status().contains(decimal::Status::DIVISION_BY_ZERO));
    /// # }
    pub struct Status: ::libc::uint32_t {
        /// Conversion syntax error.
        const CONVERSION_SYNTAX    = 0x00000001;
        /// Division by zero.
        const DIVISION_BY_ZERO     = 0x00000002;
        /// Division impossible.
        const DIVISION_IMPOSSIBLE  = 0x00000004;
        /// Division undefined.
        const DIVISION_UNDEFINED   = 0x00000008;
        // const INSUFFICIENT_STORAGE = 0x00000010;
        /// The result is inexact.
        const INEXACT              = 0x00000020;
        // const INVALID_CONTEXT      = 0x00000040;
        /// An invalid operation was requested.
        const INVALID_OPERATION    = 0x00000080;
        // const LOST_DIGITS          = 0x00000100;
        /// Overflow.
        const OVERFLOW             = 0x00000200;
        // const CLAMPED              = 0x00000400;
        // const ROUNDED              = 0x00000800;
        // const SUBNORMAL            = 0x00001000;
        /// Underflow.
        const UNDERFLOW            = 0x00002000;
    }
}
