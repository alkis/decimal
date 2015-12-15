use super::Class;
use super::Status;
use super::Rounding;

use context::*;
use libc::{c_char, int32_t, uint8_t, uint32_t};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use std::cell::RefCell;
use std::ffi::{CStr, CString};
use std::fmt;
use std::mem::uninitialized;
use std::ops::{Add, Sub, Mul, Div, Rem, Neg, BitAnd, BitOr, BitXor, Not, Shl, Shr};
use std::str::FromStr;
use std::str::from_utf8_unchecked;
use std::num::FpCategory;

thread_local!(static CTX: RefCell<Context> = RefCell::new(d128::default_context()));

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

#[cfg(feature = "rustc-serialize")]
impl Decodable for d128 {
    fn decode<D: Decoder>(d: &mut D) -> Result<Self, D::Error> {
        let s = try!(d.read_str());
        Ok(Self::from_str(&s).expect("unreachable"))
    }
}

#[cfg(feature = "rustc-serialize")]
impl Encodable for d128 {
    fn encode<E: Encoder>(&self, e: &mut E) -> Result<(), E::Error> {
        e.emit_str(&format!("{}", self))
    }
}

/// Converts an i32 to d128. The result is exact and no error is possible.
impl From<i32> for d128 {
    fn from(val: i32) -> d128 {
        unsafe {
            let mut res: d128 = uninitialized();
            *decQuadFromInt32(&mut res, val)
        }
    }
}

/// Converts an u32 to d128. The result is exact and no error is possible.
impl From<u32> for d128 {
    fn from(val: u32) -> d128 {
        unsafe {
            let mut res: d128 = uninitialized();
            *decQuadFromUInt32(&mut res, val)
        }
    }
}

impl AsRef<d128> for d128 {
    fn as_ref(&self) -> &d128 {
        &self
    }
}

/// Converts a string to d128. The length of the coefficient and the size of the exponent are
/// checked by this routine, so rounding will be applied if necessary, and this may set status
/// flags (`UNDERFLOW`, `OVERFLOW`) will be reported, or rounding applied, as necessary. There is
/// no limit to the coefficient length for finite inputs; NaN payloads must be integers with no
/// more than 33 digits. Exponents may have up to nine significant digits. The syntax of the string
/// is fully checked; if it is not valid, the result will be a quiet NaN and an error flag will be
/// set.
impl FromStr for d128 {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, ()> {
        let cstr = match CString::new(s) {
            Err(..) => CString::new("qNaN").unwrap(),
            Ok(cstr) => cstr,
        };
        d128::with_context(|ctx| {
            let mut res: d128;
            unsafe {
                res = uninitialized();
                decQuadFromString(&mut res, cstr.as_ptr(), ctx);
            }
            Ok(res)
        })
    }
}

/// Converts this d128 to an i32. It uses Rounding::HalfEven.
impl Into<i32> for d128 {
    fn into(self) -> i32 {
        d128::with_context(|ctx| unsafe { decQuadToInt32(&self, ctx, ctx.rounding) })
    }
}

/// Converts this d128 to an u32. It uses Rounding::HalfEven.
impl Into<u32> for d128 {
    fn into(self) -> u32 {
        d128::with_context(|ctx| unsafe { decQuadToUInt32(&self, ctx, ctx.rounding) })
    }
}

/// Formats a d128. Finite numbers will be converted to a string with exponential notation if the
/// exponent is positive or if the magnitude of x is less than 1 and would require more than five
/// zeros between the decimal point and the first significant digit. Note that strings which are
/// not simply numbers (one of Infinity, –Infinity, NaN, or sNaN) are possible. A NaN string may
/// have a leading – sign and/or following payload digits. No digits follow the NaN string if the
/// payload is 0.
impl fmt::Display for d128 {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = [0 as i8; 43];
        unsafe {
            decQuadToString(self, buf.as_mut().as_mut_ptr());
            let cstr = CStr::from_ptr(buf.as_ptr());
            fmt.pad(from_utf8_unchecked(cstr.to_bytes()))
        }
    }
}

/// Same as `fmt::Display`.
impl fmt::Debug for d128 {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, fmt)
    }
}

/// Formats a d128 with engineering notation. This is the same as fmt::Display except that if
/// exponential notation is used the exponent will be a multiple of 3.
impl fmt::LowerExp for d128 {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = [0 as i8; 43];
        unsafe {
            decQuadToEngString(self, buf.as_mut().as_mut_ptr());
            let cstr = CStr::from_ptr(buf.as_ptr());
            fmt.pad(from_utf8_unchecked(cstr.to_bytes()))
        }
    }
}

/// Formats a d128 to hexadecimal binary representation.
impl fmt::LowerHex for d128 {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        for b in self.bytes.iter().rev() {
            try!(write!(fmt, "{:02x}", b));
        }
        Ok(())
    }
}

impl PartialEq<d128> for d128 {
    fn eq(&self, other: &d128) -> bool {
        self.compare(other).is_zero()
    }
}

impl PartialOrd<d128> for d128 {
    fn partial_cmp(&self, other: &d128) -> Option<::std::cmp::Ordering> {
        use std::cmp::Ordering;
        match self.compare(other) {
            v if v.is_nan() => None,
            v if v.is_zero() => Some(Ordering::Equal),
            v if v.is_positive() => Some(Ordering::Greater),
            v if v.is_negative() => Some(Ordering::Less),
            _ => unreachable!(),
        }
    }
}

macro_rules! ffi_unary_op {
    ($(#[$attr:meta])* impl $op:ident, $method:ident, $ffi:ident for $t:ident) => {
        $(#[$attr])*
        impl $op for $t {
            type Output = $t;

            fn $method(mut self) -> $t {
                $t::with_context(|ctx| {
                    unsafe { *$ffi(&mut self, &self, ctx)}
                })
            }
        }

        impl<'a> $op for &'a $t {
            type Output = $t;

            fn $method(self) -> $t {
                $t::with_context(|ctx| {
                    unsafe { let mut res: $t = uninitialized(); *$ffi(&mut res, self, ctx)}
                })
            }
        }
    }
}

macro_rules! ffi_binary_op {
    ($(#[$attr:meta])* impl $op:ident, $method:ident, $ffi:ident for $t:ident) => {
        $(#[$attr])*
        impl $op<$t> for $t {
            type Output = $t;

            fn $method(mut self, other: $t) -> $t {
                $t::with_context(|ctx| {
                    unsafe { *$ffi(&mut self, &self, &other, ctx)}
                })
            }
        }

        impl<'a> $op<$t> for &'a $t {
            type Output = $t;

            fn $method(self, mut other: $t) -> $t {
                $t::with_context(|ctx| {
                    unsafe { *$ffi(&mut other, self, &other, ctx) }
                })
            }
        }

        impl<'a> $op<&'a$t> for $t {
            type Output = $t;

            fn $method(mut self, other: &'a $t) -> $t {
                $t::with_context(|ctx| {
                    unsafe { *$ffi(&mut self, &self, other, ctx) }
                })
            }
        }

        impl<'a, 'b> $op<&'a $t> for &'b $t {
            type Output = $t;

            fn $method(self, other: &'a $t) -> $t {
                $t::with_context(|ctx| {
                    unsafe { let mut res: $t = uninitialized(); *$ffi(&mut res, self, other, ctx) }
                })
            }
        }
    }
}

ffi_binary_op!(impl Add, add, decQuadAdd for d128);
ffi_binary_op!(impl Sub, sub, decQuadSubtract for d128);
ffi_binary_op!(impl Mul, mul, decQuadMultiply for d128);
ffi_binary_op!(impl Div, div, decQuadDivide for d128);
ffi_binary_op!(
    /// The operands must be zero or positive, an integer (finite with zero exponent) and comprise
    /// only zeros and/or ones; if not, INVALID_OPERATION is set.
    impl BitAnd, bitand, decQuadAnd for d128);
ffi_binary_op!(
    /// The operands must be zero or positive, an integer (finite with zero exponent) and comprise
    /// only zeros and/or ones; if not, INVALID_OPERATION is set.
    impl BitOr, bitor, decQuadOr for d128);
ffi_binary_op!(
    /// The operands must be zero or positive, an integer (finite with zero exponent) and comprise
    /// only zeros and/or ones; if not, INVALID_OPERATION is set.
    impl BitXor, bitxor, decQuadXor for d128);
ffi_binary_op!(impl Rem, rem, decQuadRemainder for d128);

ffi_unary_op!(impl Neg, neg, decQuadMinus for d128);
ffi_unary_op!(
    /// The operand must be zero or positive, an integer (finite with zero exponent) and comprise
    /// only zeros and/or ones; if not, INVALID_OPERATION is set.
    impl Not, not, decQuadInvert for d128);

/// The result is `self` with the digits of the coefficient shifted to the left without adjusting
/// the exponent or the sign of `self`. Any digits ‘shifted in’ from the right will be 0. `amount`
/// is the count of positions to shift and must be a in the range –34 through +34. NaNs are
/// propagated as usual. If `self` is infinite the result is Infinity of the same sign. No status
/// is set unless `amount` is invalid or `self` is an sNaN.
impl Shl<usize> for d128 {
    type Output = d128;

    fn shl(mut self, amount: usize) -> d128 {
        let shift = d128::from(amount as u32);
        d128::with_context(|ctx| unsafe { *decQuadShift(&mut self, &self, &shift, ctx) })
    }
}

impl<'a> Shl<usize> for &'a d128 {
    type Output = d128;

    fn shl(self, amount: usize) -> d128 {
        let shift = d128::from(amount as u32);
        d128::with_context(|ctx| {
            unsafe {
                let mut res: d128 = uninitialized();
                *decQuadShift(&mut res, self, &shift, ctx)
            }
        })
    }
}

/// The result is `self` with the digits of the coefficient shifted to the right without adjusting
/// the exponent or the sign of `self`. Any digits ‘shifted in’ from the left will be 0. `amount`
/// is the count of positions to shift and must be a in the range –34 through +34. NaNs are
/// propagated as usual. If `self` is infinite the result is Infinity of the same sign. No status
/// is set unless `amount` is invalid or `self` is an sNaN.
impl Shr<usize> for d128 {
    type Output = d128;

    fn shr(mut self, amount: usize) -> d128 {
        let shift = -d128::from(amount as u32);
        d128::with_context(|ctx| unsafe { *decQuadShift(&mut self, &self, &shift, ctx) })
    }
}

impl<'a> Shr<usize> for &'a d128 {
    type Output = d128;

    fn shr(self, amount: usize) -> d128 {
        let shift = -d128::from(amount as u32);
        d128::with_context(|ctx| {
            unsafe {
                let mut res: d128 = uninitialized();
                *decQuadShift(&mut res, self, &shift, ctx)
            }
        })
    }
}

impl d128 {
    fn default_context() -> Context {
        unsafe {
            let mut res: Context = uninitialized();
            *decContextDefault(&mut res, 128)
        }
    }

    fn with_context<F, R>(f: F) -> R
        where F: FnOnce(&mut Context) -> R
    {
        CTX.with(|ctx| f(&mut ctx.borrow_mut()))
    }

    /// Returns the thread local status.
    pub fn get_status() -> Status {
        d128::with_context(|ctx| Status::from_bits_truncate(ctx.status))
    }

    /// Sets the thread local status.
    pub fn set_status(status: Status) {
        d128::with_context(|ctx| ctx.status = status.bits());
    }

    /// Reads the hex binary representation from a string. This is the reverse of formatting with
    /// {:x}.
    pub fn from_hex(s: &str) -> d128 {
        if s.len() != 32 {
            Self::from_str("qNaN").unwrap()
        } else {
            unsafe {
                let mut res: d128 = uninitialized();
                for (i, octet) in s.as_bytes().chunks(2).rev().enumerate() {
                    res.bytes[i] = match u8::from_str_radix(from_utf8_unchecked(octet), 16) {
                        Ok(val) => val,
                        Err(..) => return Self::from_str("qNaN").unwrap(),
                    };
                }
                res
            }
        }
    }

    // Utilities and conversions, extractors, etc.

    /// Returns the d128 representing +0.
    pub fn zero() -> d128 {
        unsafe {
            let mut res = uninitialized();
            *decQuadZero(&mut res)
        }
    }

    // Computational.

    /// Returns the absolute value of `self`.
    pub fn abs(mut self) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadAbs(&mut self, &self, ctx) })
    }

    /// Calculates the fused multiply-add `self` × `a` + `b` and returns the result. The multiply
    /// is carried out first and is exact, so this operation has only the one, final, rounding.
    pub fn mul_add<O: AsRef<d128>>(mut self, a: O, b: O) -> d128 {
        d128::with_context(|ctx| {
            unsafe { *decQuadFMA(&mut self, &self, a.as_ref(), b.as_ref(), ctx) }
        })
    }

    /// Returns the adjusted exponent of `self`, according to IEEE 754 rules. That is, the exponent
    /// returned is calculated as if the decimal point followed the first significant digit (so,
    /// for example, if `self` were 123 then the result would be 2). If `self` is infinite, the
    /// result is +Infinity. If `self` is a zero, the result is –Infinity, and the
    /// `DIVISION_BY_ZERO` flag is set. If `self` is less than zero, the absolute value of `self`
    /// is used. If `self` is 1, the result is 0. NaNs are handled (propagated) as for arithmetic
    /// operations.
    pub fn logb(mut self) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadLogB(&mut self, &self, ctx) })
    }

    /// If both `self` and `other` are numeric (not NaNs) this returns the larger of the two
    /// (compared using total ordering, to give a well-defined result). If either (but not both of)
    /// is a quiet NaN then the other argument is the result; otherwise NaNs are handled as for
    /// arithmetic operations.
    pub fn max<O: AsRef<d128>>(mut self, other: O) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadMax(&mut self, &self, other.as_ref(), ctx) })
    }

    /// If both `self` and `other`  are numeric (not NaNs) this returns the smaller of the two
    /// (compared using total ordering, to give a well-defined result). If either (but not both of)
    /// is a quiet NaN then the other argument is the result; otherwise NaNs are handled as for
    /// arithmetic operations.
    pub fn min<O: AsRef<d128>>(mut self, other: O) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadMin(&mut self, &self, other.as_ref(), ctx) })
    }

    /// Returns the ‘next’ d128 to `self` in the direction of +Infinity according to IEEE 754 rules
    /// for nextUp. The only status possible is `INVALID_OPERATION` (from an sNaN).
    pub fn next(mut self) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadNextPlus(&mut self, &self, ctx) })
    }

    /// Returns the ‘next’ d128 to `self` in the direction of –Infinity according to IEEE 754 rules
    /// for nextDown. The only status possible is `INVALID_OPERATION` (from an sNaN).
    pub fn previous(mut self) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadNextMinus(&mut self, &self, ctx) })
    }

    /// The number is set to the result of raising `self` to the power of `exp`, rounded if
    /// necessary using the settings in the context. Results will be exact when `exp` has an
    /// integral value and the result does not need to be rounded, and also will be exact in certain
    /// special cases, such as when `self` is a zero (see the arithmetic specification for details).
    /// Inexact results will always be full precision, and will almost always be correctly rounded,
    /// but may be up to 1 ulp (unit in last place) in error in rare cases. This is a mathematical
    /// function; the 106 restrictions on precision and range apply as described above, except that
    /// the normal range of values and context is allowed if `exp` has an integral value in the
    /// range –1999999997 through +999999999.
    pub fn pow<O: AsRef<d128>>(mut self, exp: O) -> d128 {
        d128::with_context(|ctx| unsafe {
            let mut num_self: decNumber = uninitialized();
            let mut num_rhs: decNumber = uninitialized();
            decimal128ToNumber(&self, &mut num_self);
            decimal128ToNumber(exp.as_ref(), &mut num_rhs);
            decNumberPower(&mut num_self, &num_self, &num_rhs, ctx);
            *decimal128FromNumber(&mut self, &num_self, ctx)
        })
    }

    /// Returns the ‘next’ d128 to `self` in the direction of `other` according to proposed IEEE
    /// 754  rules for nextAfter.  If `self` == `other` the result is `self`. If either operand is
    /// a NaN the result is as for arithmetic operations. Otherwise (the operands are numeric and
    /// different) the result of adding (or subtracting) an infinitesimal positive amount to `self`
    /// and rounding towards +Infinity (or –Infinity) is returned, depending on whether `other` is
    /// larger  (or smaller) than `self`. The addition will set flags, except that if the result is
    /// normal  (finite, non-zero, and not subnormal) no flags are set.
    pub fn towards<O: AsRef<d128>>(mut self, other: O) -> d128 {
        d128::with_context(|ctx| {
            unsafe { *decQuadNextToward(&mut self, &self, other.as_ref(), ctx) }
        })
    }

    /// Returns `self` set to have the same quantum as `other`, if possible (that is, numerically
    /// the same value but rounded or padded if necessary to have the same exponent as `other`, for
    /// example to round a monetary quantity to cents).
    pub fn quantize<O: AsRef<d128>>(mut self, other: O) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadQuantize(&mut self, &self, other.as_ref(), ctx) })
    }

    /// Returns a copy of `self` with its coefficient reduced to its shortest possible form without
    /// changing the value of the result. This removes all possible trailing zeros from the
    /// coefficient (some may remain when the number is very close to the most positive or most
    /// negative number). Infinities and NaNs are unchanged and no status is set unless `self` is
    /// an sNaN. If `self` is a zero the result exponent is 0.
    pub fn reduce(mut self) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadReduce(&mut self, &self, ctx) })
    }

    /// The result is a copy of `self` with the digits of the coefficient rotated to the left (if
    /// `amount` is positive) or to the right (if `amount` is negative) without adjusting the
    /// exponent or the sign of `self`. `amount` is the count of positions to rotate and must be a
    /// finite integer (with exponent=0) in the range -34 through +34. NaNs are propagated as
    /// usual. If `self` is infinite the result is Infinity of the same sign. No status is set
    /// unless `amount` is invalid or an operand is an sNaN.
    pub fn rotate<O: AsRef<d128>>(mut self, amount: O) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadRotate(&mut self, &self, amount.as_ref(), ctx) })
    }

    /// This calculates `self` × 10<sup>`other`</sup> and returns the result. `other` must be an
    /// integer (finite with exponent=0) in the range ±2 × (34 + 6144), typically resulting from
    /// `logb`. Underflow and overflow might occur. NaNs propagate as usual.
    pub fn scaleb<O: AsRef<d128>>(mut self, other: O) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadScaleB(&mut self, &self, other.as_ref(), ctx) })
    }

    // Comparisons.

    /// Compares `self` and `other` numerically and returns the result. The result may be –1, 0, 1,
    /// or NaN (unordered); –1 indicates that `self` is less than `other`, 0 indicates that they
    /// are numerically equal, and 1 indicates that `self` is greater than `other`. NaN is returned
    /// only if `self` or `other` is a NaN.
    pub fn compare<O: AsRef<d128>>(&self, other: O) -> d128 {
        d128::with_context(|ctx| {
            unsafe {
                let mut res: d128 = uninitialized();
                *decQuadCompare(&mut res, self, other.as_ref(), ctx)
            }
        })
    }

    /// Compares `self` and `other` using the IEEE 754 total ordering (which takes into account the
    /// exponent) and returns the result. No status is set (a signaling NaN is ordered between
    /// Infinity and NaN). The result will be –1, 0, or 1.
    pub fn compare_total<O: AsRef<d128>>(&self, other: O) -> d128 {
        d128::with_context(|ctx| {
            unsafe {
                let mut res: d128 = uninitialized();
                *decQuadCompareTotal(&mut res, self, other.as_ref(), ctx)
            }
        })
    }

    // Copies.

    /// Returns `self` ensuring that the encoding is canonical.
    pub fn canonical(mut self) -> d128 {
        unsafe { *decQuadCanonical(&mut self, &self) }
    }

    // Non-computational.

    /// Returns the class of `self`.
    pub fn class(&self) -> Class {
        unsafe { decQuadClass(self) }
    }

    /// Same as `class()` but returns `std::num::FpCategory`.
    pub fn classify(&self) -> FpCategory {
        use std::num::FpCategory::*;
        use super::Class::*;

        match self.class() {
            Qnan | Snan => Nan,
            PosInf | NegInf => Infinite,
            PosZero | NegZero => Zero,
            PosNormal | NegNormal => Normal,
            PosSubnormal | NegSubnormal => Subnormal,
        }
    }

    /// Returns the number of significant digits in `self`. If `self` is a zero or is infinite, 1
    /// is returned. If `self` is a NaN then the number of digits in the payload is returned.
    pub fn digits(&self) -> u32 {
        unsafe { decQuadDigits(self) }
    }

    /// Returns `true` if the encoding of `self` is canonical, or `false` otherwise.
    pub fn is_canonical(&self) -> bool {
        unsafe { decQuadIsCanonical(self) != 0 }
    }

    /// Returns `true` if `self` is neither infinite nor a NaN, or `false` otherwise.
    pub fn is_finite(&self) -> bool {
        unsafe { decQuadIsFinite(self) != 0 }
    }

    /// Returns `true` if `self` is finite and its exponent is zero, or `false` otherwise.
    pub fn is_integer(&self) -> bool {
        unsafe { decQuadIsInteger(self) != 0 }
    }

    /// Returns `true` if `self`  is a valid argument for logical operations (that is, `self` is
    /// zero or positive, an integer (finite with a zero exponent) and comprises only zeros and/or
    /// ones), or `false` otherwise.
    pub fn is_logical(&self) -> bool {
        unsafe { decQuadIsLogical(self) != 0 }
    }

    /// Returns `true` if the encoding of `self` is an infinity, or `false` otherwise.
    pub fn is_infinite(&self) -> bool {
        unsafe { decQuadIsInfinite(self) != 0 }
    }

    /// Returns `true` if `self` is a NaN (quiet or signaling), or `false` otherwise.
    pub fn is_nan(&self) -> bool {
        unsafe { decQuadIsNaN(self) != 0 }
    }

    /// Returns `true` if `self` is less than zero and not a NaN, or `false` otherwise.
    pub fn is_negative(&self) -> bool {
        unsafe { decQuadIsNegative(self) != 0 }
    }

    /// Returns `true` if `self` is a normal number (that is, is finite, non-zero, and not
    /// subnormal), or `false` otherwise.
    pub fn is_normal(&self) -> bool {
        unsafe { decQuadIsNormal(self) != 0 }
    }

    /// Returns `true` if `self` is greater than zero and not a NaN, or `false` otherwise.
    pub fn is_positive(&self) -> bool {
        unsafe { decQuadIsPositive(self) != 0 }
    }

    /// Returns `true` if `self` is a signaling NaN, or `false` otherwise.
    pub fn is_signaling(&self) -> bool {
        unsafe { decQuadIsSignaling(self) != 0 }
    }

    /// Returns `true` if `self` has a minus sign, or `false` otherwise. Note that zeros and NaNs
    /// may have a minus sign.
    pub fn is_signed(&self) -> bool {
        unsafe { decQuadIsSigned(self) != 0 }
    }

    /// Returns `true` if `self` is subnormal (that is, finite, non-zero, and with magnitude less
    /// than 10<sup>-6143</sup>), or `false` otherwise.
    pub fn is_subnormal(&self) -> bool {
        unsafe { decQuadIsSubnormal(self) != 0 }
    }

    /// Returns `true` if `self` is zero, or `false` otherwise.
    pub fn is_zero(&self) -> bool {
        unsafe { decQuadIsZero(self) != 0 }
    }
}

extern "C" {
    // Context.
    fn decContextDefault(ctx: *mut Context, kind: uint32_t) -> *mut Context;
    // Utilities and conversions, extractors, etc.
    fn decQuadFromInt32(res: *mut d128, src: int32_t) -> *mut d128;
    fn decQuadFromString(res: *mut d128, s: *const c_char, ctx: *mut Context) -> *mut d128;
    fn decQuadFromUInt32(res: *mut d128, src: uint32_t) -> *mut d128;
    fn decQuadToString(src: *const d128, s: *mut c_char) -> *mut c_char;
    fn decQuadToInt32(src: *const d128, ctx: *mut Context, round: Rounding) -> int32_t;
    fn decQuadToUInt32(src: *const d128, ctx: *mut Context, round: Rounding) -> uint32_t;
    fn decQuadToEngString(res: *const d128, s: *mut c_char) -> *mut c_char;
    fn decQuadZero(res: *mut d128) -> *mut d128;
    // Computational.
    fn decQuadAbs(res: *mut d128, src: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadAdd(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadAnd(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadDivide(res: *mut d128,
                     a: *const d128,
                     b: *const d128,
                     ctx: *mut Context)
                     -> *mut d128;
    fn decQuadFMA(res: *mut d128,
                  a: *const d128,
                  b: *const d128,
                  c: *const d128,
                  ctx: *mut Context)
                  -> *mut d128;
    fn decQuadInvert(res: *mut d128, src: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadLogB(res: *mut d128, src: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadMax(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadMin(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadMinus(res: *mut d128, src: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadMultiply(res: *mut d128,
                       a: *const d128,
                       b: *const d128,
                       ctx: *mut Context)
                       -> *mut d128;
    fn decQuadNextMinus(res: *mut d128, src: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadNextPlus(res: *mut d128, src: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadNextToward(res: *mut d128,
                         src: *const d128,
                         other: *const d128,
                         ctx: *mut Context)
                         -> *mut d128;
    fn decQuadOr(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadQuantize(res: *mut d128,
                       a: *const d128,
                       b: *const d128,
                       ctx: *mut Context)
                       -> *mut d128;
    fn decQuadReduce(res: *mut d128, src: *const d128, ctx: *mut Context) -> *mut d128;
    fn decQuadRemainder(res: *mut d128,
                        a: *const d128,
                        b: *const d128,
                        ctx: *mut Context)
                        -> *mut d128;
    fn decQuadRotate(res: *mut d128,
                     a: *const d128,
                     b: *const d128,
                     ctx: *mut Context)
                     -> *mut d128;
    fn decQuadScaleB(res: *mut d128,
                     a: *const d128,
                     b: *const d128,
                     ctx: *mut Context)
                     -> *mut d128;
    fn decQuadShift(res: *mut d128,
                    a: *const d128,
                    b: *const d128,
                    ctx: *mut Context)
                    -> *mut d128;
    fn decQuadSubtract(res: *mut d128,
                       a: *const d128,
                       b: *const d128,
                       ctx: *mut Context)
                       -> *mut d128;
    fn decQuadXor(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut Context) -> *mut d128;
    // Comparisons.
    fn decQuadCompare(res: *mut d128,
                      a: *const d128,
                      b: *const d128,
                      ctx: *mut Context)
                      -> *mut d128;
    fn decQuadCompareTotal(res: *mut d128,
                           a: *const d128,
                           b: *const d128,
                           ctx: *mut Context)
                           -> *mut d128;
    // Copies.
    fn decQuadCanonical(res: *mut d128, src: *const d128) -> *mut d128;
    // Non-computational.
    fn decQuadClass(src: *const d128) -> Class;
    fn decQuadDigits(src: *const d128) -> uint32_t;
    fn decQuadIsCanonical(src: *const d128) -> uint32_t;
    fn decQuadIsFinite(src: *const d128) -> uint32_t;
    fn decQuadIsInteger(src: *const d128) -> uint32_t;
    fn decQuadIsLogical(src: *const d128) -> uint32_t;
    fn decQuadIsInfinite(src: *const d128) -> uint32_t;
    fn decQuadIsNaN(src: *const d128) -> uint32_t;
    fn decQuadIsNegative(src: *const d128) -> uint32_t;
    fn decQuadIsNormal(src: *const d128) -> uint32_t;
    fn decQuadIsPositive(src: *const d128) -> uint32_t;
    fn decQuadIsSignaling(src: *const d128) -> uint32_t;
    fn decQuadIsSigned(src: *const d128) -> uint32_t;
    fn decQuadIsSubnormal(src: *const d128) -> uint32_t;
    fn decQuadIsZero(src: *const d128) -> uint32_t;
    // decNumber stuff.
    fn decimal128FromNumber(res: *mut d128, src: *const decNumber, ctx: *mut Context) -> *mut d128;
    fn decimal128ToNumber(src: *const d128, res: *mut decNumber) -> *mut decNumber;
    fn decNumberPower(res: *mut decNumber,
                      lhs: *const decNumber,
                      rhs: *const decNumber,
                      ctx: *mut Context)
                      -> *mut decNumber;
}

#[cfg(test)]
mod tests {
    use super::*;

    use rustc_serialize::json;

    #[cfg(feature = "rustc-serialize")]
    #[test]
    fn test_rustc_serialize() {
        #[derive(RustcDecodable, RustcEncodable, PartialEq, Debug)]
        struct Test {
            price: d128,
        };
        let a = Test { price: d128!(12.3456) };
        assert_eq!(json::encode(&a).unwrap(), "{\"price\":\"12.3456\"}");
        let b = json::decode("{\"price\":\"12.3456\"}").unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn unary_op() {
        assert_eq!(d128!(-1.1), -d128!(1.1));
        assert_eq!(d128!(-1.1), -&d128!(1.1));
    }

    #[test]
    fn binary_op() {
        assert_eq!(d128!(3.33), d128!(1.11) + d128!(2.22));
        assert_eq!(d128!(3.33), &d128!(1.11) + d128!(2.22));
        assert_eq!(d128!(3.33), d128!(1.11) + &d128!(2.22));
        assert_eq!(d128!(3.33), &d128!(1.11) + &d128!(2.22));
    }

    #[test]
    fn as_ref_operand() {
        assert_eq!(d128!(1.1), d128!(1.1).min(d128!(2.2)));
        assert_eq!(d128!(1.1), d128!(1.1).min(&d128!(2.2)));
    }
}
