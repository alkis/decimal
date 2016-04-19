#[repr(C)]
#[derive(Clone, Copy)]
/// A 128-bit decimal floating point type.
pub struct d128 {
    bytes: [uint8_t; 16],
}

#[repr(C)]
#[derive(Clone, Copy)]
struct decNumber {
    digits: i32,
    exponent: i32,
    bits: u8,
    // DECPUN = 3 because this is the fastest for conversion between decNumber and decQuad
    // DECNUMDIGITS = 34 because we use decQuad only
    // 12 = ((DECNUMDIGITS+DECDPUN-1)/DECDPUN)
    lsu: [u16; 12],
}

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
    /// # #[macro_use]
    /// # extern crate decimal;
    /// # use decimal::d128;
    /// # use decimal::Status;
    /// # fn main() {
    /// assert_eq!(d128::get_status(), Status::empty());
    /// let _ = d128!(1) / &d128!(0);
    /// assert!(d128::get_status().contains(decimal::DIVISION_BY_ZERO));
    /// let _ = d128!(0) / &d128!(0);
    /// assert!(d128::get_status().contains(decimal::DIVISION_UNDEFINED));
    /// // The previous status flag was not cleared!
    /// assert!(d128::get_status().contains(decimal::DIVISION_BY_ZERO));
    /// # }
    pub flags Status: ::libc::uint32_t {
        /// Conversion syntax error.
        const CONVERSION_SYNTAX    = 0x00000001,
        /// Division by zero.
        const DIVISION_BY_ZERO     = 0x00000002,
        /// Division impossible.
        const DIVISION_IMPOSSIBLE  = 0x00000004,
        /// Division undefined.
        const DIVISION_UNDEFINED   = 0x00000008,
        // const INSUFFICIENT_STORAGE = 0x00000010,
        /// The result is inexact.
        const INEXACT              = 0x00000020,
        // const INVALID_CONTEXT      = 0x00000040,
        /// An invalid operation was requested.
        const INVALID_OPERATION    = 0x00000080,
        // const LOST_DIGITS          = 0x00000100,
        /// Overflow.
        const OVERFLOW             = 0x00000200,
        // const CLAMPED              = 0x00000400,
        // const ROUNDED              = 0x00000800,
        // const SUBNORMAL            = 0x00001000,
        /// Underflow.
        const UNDERFLOW            = 0x00002000,
    }
}
