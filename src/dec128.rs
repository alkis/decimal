use super::Class;
use super::Status;
use super::Rounding;

use context::*;
use libc::{c_char, int32_t, uint8_t, uint32_t};
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
#[derive(Clone, Copy, Debug)]
/// A 128-bit decimal floating point type.
pub struct d128 {
    bytes: [uint8_t; 16],
}

/// Converts an i32 to d128. The result is exact and no error is possible.
impl From<i32> for d128 {
    fn from(val: i32) -> d128 {
        unsafe {
            let mut res: d128 = uninitialized();
            decQuadFromInt32(&mut res, val);
            res
        }
    }
}

/// Converts an u32 to d128. The result is exact and no error is possible.
impl From<u32> for d128 {
    fn from(val: u32) -> d128 {
        let mut res: d128;
        unsafe {
            res = uninitialized();
            decQuadFromUInt32(&mut res, val);
        };
        res
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
        Self::with_context(|ctx| {
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
        Self::with_context(|ctx| unsafe { decQuadToInt32(&self, ctx, ctx.rounding) })
    }
}

/// Converts this d128 to an u32. It uses Rounding::HalfEven.
impl Into<u32> for d128 {
    fn into(self) -> u32 {
        Self::with_context(|ctx| unsafe { decQuadToUInt32(&self, ctx, ctx.rounding) })
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

impl<'a> Add<&'a d128> for d128 {
    type Output = d128;

    fn add(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadAdd(&mut self, &self, other, ctx) };
            self
        })
    }
}

impl<'a> Sub<&'a d128> for d128 {
    type Output = d128;

    fn sub(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadSubtract(&mut self, &self, other, ctx) };
            self
        })
    }

}

impl<'a> Mul<&'a d128> for d128 {
    type Output = d128;

    fn mul(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadMultiply(&mut self, &self, other, ctx) };
            self
        })
    }
}

impl<'a> Div<&'a d128> for d128 {
    type Output = d128;

    fn div(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadDivide(&mut self, &self, other, ctx) };
            self
        })
    }
}

impl<'a> Rem<&'a d128> for d128 {
    type Output = d128;

    fn rem(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadRemainder(&mut self, &self, other, ctx) };
            self
        })
    }
}

impl Neg for d128 {
    type Output = d128;

    fn neg(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadMinus(&mut self, &self, ctx) };
            self
        })
    }
}

/// The operands must be zero or positive, an integer (finite with zero exponent) and comprise only
/// zeros and/or ones; if not, INVALID_OPERATION is set.
impl<'a> BitAnd<&'a d128> for d128 {
    type Output = d128;

    fn bitand(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadAnd(&mut self, &self, other, ctx) };
            self
        })
    }
}

/// The operands must be zero or positive, an integer (finite with zero exponent) and comprise only
/// zeros and/or ones; if not, INVALID_OPERATION is set.
impl<'a> BitOr<&'a d128> for d128 {
    type Output = d128;

    fn bitor(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadOr(&mut self, &self, other, ctx) };
            self
        })
    }
}

/// The operands must be zero or positive, an integer (finite with zero exponent) and comprise only
/// zeros and/or ones; if not, INVALID_OPERATION is set.
impl<'a> BitXor<&'a d128> for d128 {
    type Output = d128;

    fn bitxor(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadXor(&mut self, &self, other, ctx) };
            self
        })
    }
}

/// The result is `self` with the digits of the coefficient shifted to the left without adjusting
/// the exponent or the sign of `self`. Any digits ‘shifted in’ from the right will be 0. `amount`
/// is the count of positions to shift and must be a in the range –34 through +34. NaNs are
/// propagated as usual. If `self` is infinite the result is Infinity of the same sign. No status
/// is set unless `amount` is invalid or `self` is an sNaN.
impl Shl<usize> for d128 {
    type Output = d128;

    fn shl(mut self, amount: usize) -> d128 {
        let shift = d128::from(amount as u32);
        Self::with_context(|ctx| {
            unsafe { decQuadShift(&mut self, &self, &shift, ctx) };
            self
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
        Self::with_context(|ctx| {
            unsafe { decQuadShift(&mut self, &self, &shift, ctx) };
            self
        })
    }
}

/// The operand must be zero or positive, an integer (finite with zero exponent) and comprise only
/// zeros and/or ones; if not, INVALID_OPERATION is set.
impl Not for d128 {
    type Output = d128;

    fn not(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadInvert(&mut self, &self, ctx) };
            self
        })
    }
}

impl d128 {
    fn default_context() -> Context {
        unsafe {
            let mut res: Context = uninitialized();
            decContextDefault(&mut res, 128);
            // assert_eq!(res.digits, 34);
            // assert_eq!(res.emin, -6143);
            // assert_eq!(res.emax, 6144);
            // assert_eq!(res.rounding, Rounding::HalfEven);
            // assert_eq!(res.status, 0);
            // assert_eq!(res.clamp, 1);
            res
        }
    }

    fn with_context<F, R>(f: F) -> R
        where F: FnOnce(&mut Context) -> R
    {
        CTX.with(|ctx| f(&mut ctx.borrow_mut()))
    }

    /// Returns the thread local status.
    pub fn get_status() -> Status {
        Self::with_context(|ctx| Status::from_bits_truncate(ctx.status))
    }

    /// Sets the thread local status.
    pub fn set_status(status: Status) {
        Self::with_context(|ctx| ctx.status = status.bits());
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
            decQuadZero(&mut res);
            res
        }
    }

    // Computational.

    /// Returns the absolute value of `self`.
    pub fn abs(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadAbs(&mut self, &self, ctx) };
            self
        })
    }

    /// Calculates the fused multiply-add `self` × `a` + `b` and returns the result. The multiply
    /// is carried out first and is exact, so this operation has only the one, final, rounding.
    pub fn mul_add<'a, 'b>(mut self, a: &'a d128, b: &'b d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadFMA(&mut self, &self, a, b, ctx) };
            self
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
        Self::with_context(|ctx| {
            unsafe { decQuadLogB(&mut self, &self, ctx) };
            self
        })
    }

    /// If both `self` and `other` are numeric (not NaNs) this returns the larger of the two
    /// (compared using total ordering, to give a well-defined result). If either (but not both of)
    /// is a quiet NaN then the other argument is the result; otherwise NaNs are handled as for
    /// arithmetic operations.
    pub fn max(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadMax(&mut self, &self, other, ctx) };
            self
        })
    }

    /// If both `self` and `other`  are numeric (not NaNs) this returns the smaller of the two ///
    /// (compared using total ordering, to give a well-defined result). If either (but not both of) /// ///
    /// is a quiet NaN then the other argument is the result; otherwise NaNs are handled as /// for ///
    /// arithmetic operations.
    pub fn min(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadMin(&mut self, &self, other, ctx) };
            self
        })
    }

    /// Returns the ‘next’ d128 to `self` in the direction of +Infinity according to IEEE 754 rules
    /// for nextUp. The only status possible is `INVALID_OPERATION` (from an sNaN).
    pub fn next(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadNextPlus(&mut self, &self, ctx) };
            self
        })
    }

    /// Returns the ‘next’ d128 to `self` in the direction of –Infinity according to IEEE 754 rules
    /// for nextDown. The only status possible is `INVALID_OPERATION` (from an sNaN).
    pub fn previous(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadNextMinus(&mut self, &self, ctx) };
            self
        })
    }

    /// Returns the ‘next’ d128 to `self` in the direction of `other` according to proposed IEEE
    /// 754  rules for nextAfter.  If `self` == `other` the result is `self`. If either operand is
    /// a NaN the result is as for arithmetic operations. Otherwise (the operands are numeric and
    /// different) the result of adding (or subtracting) an infinitesimal positive amount to `self`
    /// and rounding towards +Infinity (or –Infinity) is returned, depending on whether `other` is
    /// larger  (or smaller) than `self`. The addition will set flags, except that if the result is
    /// normal  (finite, non-zero, and not subnormal) no flags are set.
    pub fn towards(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadNextToward(&mut self, &self, other, ctx) };
            self
        })
    }

    /// Returns `self` set to have the same quantum as `other`, if possible (that is, numerically
    /// the same value but rounded or padded if necessary to have the same exponent as `other`, for
    /// example to round a monetary quantity to cents).
    pub fn quantize(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadQuantize(&mut self, &self, other, ctx) };
            self
        })
    }

    /// Returns a copy of `self` with its coefficient reduced to its shortest possible form without
    /// changing the value of the result. This removes all possible trailing zeros from the
    /// coefficient (some may remain when the number is very close to the most positive or most
    /// negative number). Infinities and NaNs are unchanged and no status is set unless `self` is
    /// an sNaN. If `self` is a zero the result exponent is 0.
    pub fn reduce(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadReduce(&mut self, &self, ctx) };
            self
        })
    }

    /// The result is a copy of `self` with the digits of the coefficient rotated to the left (if
    /// `amount` is positive) or to the right (if `amount` is negative) without adjusting the
    /// exponent or the sign of `self`. `amount` is the count of positions to rotate and must be a
    /// finite integer (with exponent=0) in the range -34 through +34. NaNs are propagated as
    /// usual. If `self` is infinite the result is Infinity of the same sign. No status is set
    /// unless `amount` is invalid or an operand is an sNaN.
    pub fn rotate(mut self, amount: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadRotate(&mut self, &self, amount, ctx) };
            self
        })
    }

    /// This calculates `self` × 10<sup>`other`</sup> and returns the result. `other` must be an
    /// integer (finite with exponent=0) in the range ±2 × (34 + 6144), typically resulting from
    /// `logb`. Underflow and overflow might occur. NaNs propagate as usual.
    pub fn scaleb(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadScaleB(&mut self, &self, other, ctx) };
            self
        })
    }

    // Comparisons.

    /// Compares `self` and `other` numerically and returns the result. The result may be –1, 0, 1,
    /// or NaN (unordered); –1 indicates that `self` is less than `other`, 0 indicates that they
    /// are numerically equal, and 1 indicates that `self` is greater than `other`. NaN is returned
    /// only if `self` or `other` is a NaN.
    pub fn compare(&self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            let mut res: d128;
            unsafe {
                res = uninitialized();
                decQuadCompare(&mut res, self, other, ctx);
            }
            res
        })
    }

    /// Compares `self` and `other` using the IEEE 754 total ordering (which takes into account the
    /// exponent) and returns the result. No status is set (a signaling NaN is ordered between
    /// Infinity and NaN). The result will be –1, 0, or 1.
    pub fn compare_total(&self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            let mut res: d128;
            unsafe {
                res = uninitialized();
                decQuadCompareTotal(&mut res, self, other, ctx);
            }
            res
        })
    }

    // Copies.

    /// Returns `self` ensuring that the encoding is canonical.
    pub fn canonical(mut self) -> d128 {
        unsafe { decQuadCanonical(&mut self, &self) };
        self
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

extern {
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
}
