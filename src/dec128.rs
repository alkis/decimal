use super::Class;
use super::Status;
use super::Rounding;

use context::*;
use libc::{c_char, int32_t, uint8_t, uint32_t};
#[cfg(feature = "ord_subset")]
use ord_subset;
#[cfg(feature = "rustc-serialize")]
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
#[cfg(feature = "serde")]
use serde;
#[cfg(feature = "slog")]
use slog;
use std::borrow::Borrow;
use std::cell::RefCell;
use std::default::Default;
use std::ffi::{CStr, CString};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter::Sum;
use std::mem::uninitialized;
use std::num::FpCategory;
use std::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Div, DivAssign, Rem, RemAssign,
               Neg, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl,
               ShlAssign, Shr, ShrAssign, Deref};
use std::str::FromStr;
use std::str::from_utf8_unchecked;
use std::{f32, f64};

thread_local!(static CTX: RefCell<Context> = RefCell::new(d128::default_context()));
thread_local!(static ROUND_DOWN: RefCell<Context> = RefCell::new(d128::with_rounding(Rounding::Down)));
thread_local!(static HALF_UP: RefCell<Context> = RefCell::new(d128::with_rounding(Rounding::HalfUp)));

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

impl Default for d128 {
    fn default() -> Self {
        d128::zero()
    }
}

#[cfg(feature = "ord_subset")]
impl ord_subset::OrdSubset for d128 {
    fn is_outside_order(&self) -> bool {
        self.is_nan()
    }
}

#[cfg(feature = "ord_subset")]
impl From<d128> for ord_subset::OrdVar<d128> {
    fn from(val: d128) -> ord_subset::OrdVar<d128> {
        ord_subset::OrdVar::new(val)
    }
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

impl Hash for d128 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}

#[cfg(feature = "serde")]
impl serde::ser::Serialize for d128 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::ser::Serializer
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::de::Deserialize<'de> for d128 {
    fn deserialize<D>(deserializer: D) -> Result<d128, D::Error>
        where D: serde::de::Deserializer<'de>
    {
        deserializer.deserialize_str(d128Visitor)
    }
}

#[cfg(feature = "serde")]
#[allow(non_camel_case_types)]
struct d128Visitor;

#[cfg(feature = "serde")]
impl<'de> serde::de::Visitor<'de> for d128Visitor {
    type Value = d128;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a d128 value")
    }

    fn visit_str<E>(self, s: &str) -> Result<d128, E>
        where E: serde::de::Error
    {
        use serde::de::Unexpected;
        d128::from_str(s).map_err(|_| E::invalid_value(Unexpected::Str(s), &self))
    }
}

/// Converts an i32 to d128. The result is exact and no error is possible.
impl From<i32> for d128 {
    #[inline]
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

impl From<d128> for f64 {
    #[inline]
    fn from(x: d128) -> Self {
        if !x.is_finite() {
            if x.is_infinite() {
                if x > d128::zero() {
                    f64::INFINITY
                } else {
                    f64::NEG_INFINITY
                }
            } else {
                f64::NAN
            }
        } else {
            f64::from_str(&(format!("{}", x)))
                .unwrap_or(f64::NAN)
        }
    }
}

impl From<d128> for f32 {
    #[inline]
    fn from(x: d128) -> Self {
        if !x.is_finite() {
            if x.is_infinite() {
                if x > d128::zero() {
                    f32::INFINITY
                } else {
                    f32::NEG_INFINITY
                }
            } else {
                f32::NAN
            }
        } else {
            // for whatever reason, the f32::from_str is slow
            f64::from_str(&(format!("{}", x)))
                //.expect(&format!("f64::from_str conversion from d128: {}", x))
                .unwrap_or(f64::NAN)
                as f32
        }
    }
}

/// # Examples
/// ```
/// #[macro_use]
/// extern crate decimal;
///
/// fn main() {
///     let x = d128!(12345);
///     assert_eq!(u64::from(x), 12345u64);
/// }
/// ```
impl From<d128> for u64 {
    #[inline]
    fn from(val: d128) -> u64 {
        debug_assert!(val >= d128::zero());
        //let mut bcd = [0; 34];
        let mut bcd: [u8; 34] = unsafe { uninitialized() };
        let mut exp: i32 = unsafe { uninitialized() };
        unsafe {
            let _ = decQuadToBCD(&val, &mut exp, &mut bcd);
            //debug_assert_eq!(i, 0);
        }
        let mut u: u128 = 0;
        let mut i: usize = 33;
        let n: usize = val.digits() as usize;
        //assert!(n < 21, "val.digits() = {} (> 21); val = {}", n, val);
        while i > 33 - n {
            u += bcd[i] as u128 * 10u128.pow((33 - i) as u32);
            i -= 1;
        }
        // for (i, b) in bcd.iter().rev().enumerate().take(val.digits() as usize) {
        //     u += (*b as u64) * 10u64.pow(i as u32);
        // }
        //println!("exp = {}", exp);
        match exp {
            e if e > 0 => (u * 10u128.pow(exp as u32)) as u64,

            e if e < 0 => (u / 10u128.pow(exp.abs() as u32)) as u64,

            _ => u as u64
        }
        // if exp > 0 {
        //     u *= 10u64.pow(exp as u32);
        // } else if exp < 0 {
        //     u /= 10u64.pow(exp.abs() as u32)
        // }
        // u
        //(u * exp as i64) as u64
        // bcd.iter()
        //     .rev()
        //     .enumerate()
        //     .take(val.digits() as usize)
        //     .fold(0, |acc, (i, x)| acc + (*x as u64 ) * 10u64.pow(i as u32))
    }
}

/// Converts an u64 to d128. The result is exact and no error is possible.
impl From<u64> for d128 {
    fn from(mut val: u64) -> d128 {
        let mut bcd = [0; 34];
        let mut i = 33;
        while val > 0 {
            bcd[i] = (val % 10) as u8;
            val /= 10;
            i -= 1;
        }
        unsafe {
            let mut res: d128 = uninitialized();
            *decQuadFromBCD(&mut res, 0, bcd.as_ptr(), 0)
        }
    }
}

/// Converts an u128 to d128. The result is exact and no error is possible.
///
/// # Examples
/// ```
/// #![feature(i128, i128_type)]
/// #[macro_use]
/// extern crate decimal;
///
/// use decimal::d128;
///
/// fn main() {
///     let a: u128 = 12345;
///     assert_eq!(d128::from(a), d128!(12345));
///
///     let b: u128 = 340282366920938463463374607431768211455;
///     assert_eq!(d128::from(b), d128!(340282366920938463463374607431768211455));
///
///     let c: u128 = 999_999_999_999_999_999_999_999_999_999_999;
///     assert_eq!(d128::from(c), d128!(999999999999999999999999999999999));
///
///     let d: u128 = 9_999_999_999_999_999_999_999_999_999_999_999;
///     assert_eq!(d128::from(d), d128!(9999999999999999999999999999999999));
///
///     let e: u128 = 98_999_999_999_999_999_999_999_999_999_999_999;
///     assert_eq!(d128::from(e), d128!(98999999999999999999999999999999999));
///
///     let f: u128 = 10_000_000_000_000_000_000_000_000_000_000_000;
///     assert_eq!(d128::from(f), d128!(10000000000000000000000000000000000));
/// }
/// ```
impl From<u128> for d128 {
    fn from(mut val: u128) -> d128 {
        if val > 9_999_999_999_999_999_999_999_999_999_999_999 { // max value w/ 34 digits
            return d128::from_str(&format!("{}", val)).unwrap()
        }

        let mut bcd = [0; 34];
        let mut i = 0;
        while val > 0 && i < 34 {
            bcd[33 - i] = (val % 10) as u8;
            val /= 10;
            i += 1;
        }

        unsafe {
            let mut res: d128 = uninitialized();
            *decQuadFromBCD(&mut res, 0, bcd.as_ptr(), 0)
        }
    }
}

/// Converts an i64 to d128. The result is exact and no error is possible.
impl From<i64> for d128 {
    fn from(val: i64) -> d128 {
        if val < 0 {
            -d128::from(!(val as u64) + 1)
        } else {
            d128::from(val as u64)
        }
    }
}

impl AsRef<d128> for d128 {
    fn as_ref(&self) -> &d128 {
        &self
    }
}

impl Deref for d128 {
    type Target = [uint8_t; 16];

    fn deref(&self) -> &[uint8_t; 16] {
        &self.bytes
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
impl From<d128> for i32 {
    fn from(val: d128) -> i32 {
        d128::with_context(|ctx| unsafe { decQuadToInt32(&val, ctx, ctx.rounding) })
    }
}

/// Converts this d128 to an u32. It uses Rounding::HalfEven.
impl From<d128> for u32 {
    fn from(val: d128) -> u32 {
        d128::with_context(|ctx| unsafe { decQuadToUInt32(&val, ctx, ctx.rounding) })
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
        let mut buf = [0; 43];
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
        let mut buf = [0; 43];
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

macro_rules! ffi_unary_assign_op {
    ($(#[$attr:meta])* impl $op:ident, $method:ident, $ffi:ident for $t:ident) => {
        $(#[$attr])*
        impl $op<$t> for $t {
            fn $method(&mut self, other: $t) {
                $t::with_context(|ctx| {
                    unsafe { $ffi(self, self, &other, ctx); }
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

ffi_unary_assign_op!(impl AddAssign, add_assign, decQuadAdd for d128);
ffi_unary_assign_op!(impl SubAssign, sub_assign, decQuadSubtract for d128);
ffi_unary_assign_op!(impl MulAssign, mul_assign, decQuadMultiply for d128);
ffi_unary_assign_op!(impl DivAssign, div_assign, decQuadDivide for d128);
ffi_unary_assign_op!(impl BitAndAssign, bitand_assign, decQuadAnd for d128);
ffi_unary_assign_op!(impl BitOrAssign, bitor_assign, decQuadOr for d128);
ffi_unary_assign_op!(impl BitXorAssign, bitxor_assign, decQuadXor for d128);
ffi_unary_assign_op!(impl RemAssign, rem_assign, decQuadRemainder for d128);

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

impl ShlAssign<usize> for d128 {
    fn shl_assign(&mut self, amount: usize) {
        let shift = d128::from(amount as u32);
        d128::with_context(|ctx| {
            unsafe {
                decQuadShift(self, self, &shift, ctx);
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

impl ShrAssign<usize> for d128 {
    fn shr_assign(&mut self, amount: usize) {
        let shift = -d128::from(amount as u32);
        d128::with_context(|ctx| {
            unsafe {
                decQuadShift(self, self, &shift, ctx);
            }
        })
    }
}

impl<T> Sum<T> for d128 where T: Borrow<d128> {
    fn sum<I: IntoIterator<Item = T>>(iter: I) -> d128 {
        iter.into_iter()
            .fold(d128::zero(), |acc, val|
                acc + val.borrow())
    }
}

impl d128 {
    fn default_context() -> Context {
        unsafe {
            let mut res: Context = uninitialized();
            *decContextDefault(&mut res, 128)
        }
    }

    /// Initialize a `Context` with the specified `Rounding`.
    fn with_rounding(rounding: Rounding) -> Context {
        unsafe {
            let mut res: Context = uninitialized();
            let mut ctx = *decContextDefault(&mut res, 128);
            decContextSetRounding(&mut ctx, rounding as u32);
            ctx
        }
    }

    fn with_round_down<F, R>(f: F) -> R
        where F: FnOnce(&mut Context) -> R
    {
        ROUND_DOWN.with(|ctx| f(&mut ctx.borrow_mut()))
    }

    fn with_half_up<F, R>(f: F) -> R
        where F: FnOnce(&mut Context) -> R
    {
        HALF_UP.with(|ctx| f(&mut ctx.borrow_mut()))
    }

    fn with_context<F, R>(f: F) -> R
        where F: FnOnce(&mut Context) -> R
    {
        CTX.with(|ctx| f(&mut ctx.borrow_mut()))
    }

    /// Creates a d128 from raw bytes. Endianess is host dependent.
    pub const fn from_raw_bytes(bytes: [u8; 16]) -> d128 {
        d128 { bytes }
    }

    /// Returns raw bytes for this d128. Endianess is host dependent.
    pub fn to_raw_bytes(&self) -> [u8; 16] {
        self.bytes
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

    /// Returns the d128 representing +Infinity.
    pub fn infinity() -> d128 {
        d128!(Infinity)
    }

    /// Returns the d128 representing -Infinity.
    pub fn neg_infinity() -> d128 {
        d128!(-Infinity)
    }

    // Computational.

    /// Returns the absolute value of `self`.
    pub fn abs(mut self) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadAbs(&mut self, &self, ctx) })
    }

    /// Calculates the fused multiply-add `self` × `a` + `b` and returns the result. The multiply
    /// is carried out first and is exact, so this operation has only the one, final, rounding.
    pub fn mul_add<O: AsRef<d128>>(mut self, a: O, b: O) -> d128 {
        d128::with_context(|ctx| unsafe {
            *decQuadFMA(&mut self, &self, a.as_ref(), b.as_ref(), ctx)
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

    /// The number is set to the result of raising `self` to the power of `exp`. Results will be
    /// exact when `exp` has an integral value and the result does not need to be rounded, and also
    /// will be exact in certain special cases, such as when `self` is a zero (see the arithmetic
    /// specification for details). Inexact results will always be full precision, and will almost
    /// always be correctly rounded, but may be up to 1 _ulp_ (unit in last place) in error in rare
    /// cases. This is a mathematical function; the 10<sup>6</sup> restrictions on precision and
    /// range apply as described above, except that the normal range of values is allowed if `exp`
    /// has an integral value in the range –1999999997 through +999999999.
    pub fn pow<O: AsRef<d128>>(mut self, exp: O) -> d128 {
        d128::with_context(|ctx| unsafe {
            let mut num_self: decNumber = uninitialized();
            let mut num_exp: decNumber = uninitialized();
            decimal128ToNumber(&self, &mut num_self);
            decimal128ToNumber(exp.as_ref(), &mut num_exp);
            decNumberPower(&mut num_self, &num_self, &num_exp, ctx);
            *decimal128FromNumber(&mut self, &num_self, ctx)
        })
    }

    /// The number is set to _e_ raised to the power of `exp`. Finite results will always be full
    /// precision and inexact, except when `exp` is a zero or –Infinity (giving 1 or 0
    /// respectively). Inexact results will almost always be correctly rounded, but may be up to 1
    /// ulp (unit in last place) in error in rare cases. This is a mathematical function; the
    /// 10<sup>6</sup> restrictions on precision and range apply as described above.
    pub fn exp<O: AsRef<d128>>(mut self, exp: O) -> d128 {
        d128::with_context(|ctx| unsafe {
            let mut num_self: decNumber = uninitialized();
            let mut num_exp: decNumber = uninitialized();
            decimal128ToNumber(&self, &mut num_self);
            decimal128ToNumber(exp.as_ref(), &mut num_exp);
            decNumberExp(&mut num_self, &num_self, &num_exp, ctx);
            *decimal128FromNumber(&mut self, &num_self, ctx)
        })
    }

    /// The number is set to the natural logarithm (logarithm in base e) of `self`. `self` must be
    /// positive or a zero. Finite results will always be full precision and inexact, except when
    /// `self` is equal to 1, which gives an exact result of 0. Inexact results will almost always
    /// be correctly rounded, but may be up to 1 ulp (unit in last place) in error in rare cases.
    /// This is a mathematical function; the 10<sup>6</sup> restrictions on precision and range
    /// apply as described above.
    pub fn ln(mut self) -> d128 {
        d128::with_context(|ctx| unsafe {
            let mut num_self: decNumber = uninitialized();
            decimal128ToNumber(&self, &mut num_self);
            decNumberLn(&mut num_self, &num_self, ctx);
            *decimal128FromNumber(&mut self, &num_self, ctx)
        })
    }

    /// The number is set to the logarithm in base ten of `self`. `self` must be positive or a
    /// zero. Finite results will always be full precision and inexact, except when `self` is equal
    /// to an integral power of ten, in which case the result is the exact integer. Inexact results
    /// will almost always be correctly rounded, but may be up to 1 ulp (unit in last place) in
    /// error in rare cases. This is a mathematical function; the 10<sup>6</sup> restrictions on
    /// precision and range apply as described above.
    pub fn log10(mut self) -> d128 {
        d128::with_context(|ctx| unsafe {
            let mut num_self: decNumber = uninitialized();
            decimal128ToNumber(&self, &mut num_self);
            decNumberLog10(&mut num_self, &num_self, ctx);
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
        d128::with_context(|ctx| unsafe {
            *decQuadNextToward(&mut self, &self, other.as_ref(), ctx)
        })
    }

    /// Returns `self` set to have the same quantum as `other`, if possible (that is, numerically
    /// the same value but rounded or padded if necessary to have the same exponent as `other`, for
    /// example to round a monetary quantity to cents).
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use]
    /// extern crate decimal;
    ///
    /// fn main() {
    ///     let prec = d128!(0.1);
    ///     assert_eq!(d128!(0.400012342423).quantize(prec), d128!(0.4));
    ///     // uses default rounding (half even)
    ///     assert_eq!(d128!(0.05).quantize(prec), d128!(0.0));
    ///     assert_eq!(d128!(0.15).quantize(prec), d128!(0.2));
    /// }
    /// ```
    pub fn quantize<O: AsRef<d128>>(mut self, other: O) -> d128 {
        d128::with_context(|ctx| unsafe { *decQuadQuantize(&mut self, &self, other.as_ref(), ctx) })
    }

    /// Like `quantize`, but uses `Rounding::Down`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use]
    /// extern crate decimal;
    ///
    /// fn main() {
    ///     let prec = d128!(0.1);
    ///     assert_eq!(d128!(0.05).truncate(prec), d128!(0.0));
    ///     assert_eq!(d128!(0.15).truncate(prec), d128!(0.1));
    ///     assert_eq!(d128!(0.19).truncate(prec), d128!(0.1));
    /// }
    /// ```
    pub fn truncate<O: AsRef<d128>>(mut self, other: O) -> d128 {
        d128::with_round_down(|ctx| unsafe { *decQuadQuantize(&mut self, &self, other.as_ref(), ctx) })
    }

    /// Like `quantize`, but uses `Rounding::HalfUp`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use]
    /// extern crate decimal;
    ///
    /// fn main() {
    ///     let prec = d128!(0.1);
    ///     assert_eq!(d128!(0.15).round(prec), d128!(0.2));
    ///     assert_eq!(d128!(0.14999999999).round(prec), d128!(0.1));
    ///     assert_eq!(d128!(0.19).round(prec), d128!(0.2));
    ///     assert_eq!(d128!(0.05).round(prec), d128!(0.1));
    /// }
    /// ```
    pub fn round<O: AsRef<d128>>(mut self, other: O) -> d128 {
        d128::with_half_up(|ctx| unsafe { *decQuadQuantize(&mut self, &self, other.as_ref(), ctx) })
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
    ///
    /// # Examples
    /// ```
    /// #[macro_use]
    /// extern crate decimal;
    ///
    /// fn main() {
    ///     let x = d128!(1.2345);
    ///     let one = d128!(1);
    ///     assert_eq!(x.rotate(one), d128!(12.345));
    /// }
    /// ```
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
        d128::with_context(|ctx| unsafe {
            let mut res: d128 = uninitialized();
            *decQuadCompare(&mut res, self, other.as_ref(), ctx)
        })
    }

    /// Compares `self` and `other` using the IEEE 754 total ordering (which takes into account the
    /// exponent) and returns the result. No status is set (a signaling NaN is ordered between
    /// Infinity and NaN). The result will be –1, 0, or 1.
    pub fn compare_total<O: AsRef<d128>>(&self, other: O) -> d128 {
        d128::with_context(|ctx| unsafe {
            let mut res: d128 = uninitialized();
            *decQuadCompareTotal(&mut res, self, other.as_ref(), ctx)
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

    pub fn finite_or(self, default: d128) -> d128 {
        match self.is_finite() {
            true => self,
            false => default
        }
    }

    pub fn finite_or_else<F: FnOnce() -> d128>(self, f: F) -> d128 {
        match self.is_finite() {
            true => self,
            false => f()
        }
    }
}

#[cfg(feature = "slog")]
impl slog::Value for d128 {
    fn serialize(
        &self,
        _record: &slog::Record,
        key: slog::Key,
        serializer: &mut slog::Serializer,
    ) -> Result<(), slog::Error> {
        serializer.emit_arguments(key, &format_args!("{}", self))
    }
}

extern "C" {
    // Context.
    fn decContextDefault(ctx: *mut Context, kind: uint32_t) -> *mut Context;
    fn decContextSetRounding(ctx: *mut Context, rounding: uint32_t);
    // Utilities and conversions, extractors, etc.
    fn decQuadFromBCD(res: *mut d128, exp: i32, bcd: *const u8, sign: i32) -> *mut d128;
    fn decQuadToBCD(res: *const d128, exp: &mut i32, bcd: &mut [u8; 34]) -> int32_t;
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
    fn decNumberExp(res: *mut decNumber,
                    lhs: *const decNumber,
                    rhs: *const decNumber,
                    ctx: *mut Context)
                    -> *mut decNumber;
    fn decNumberLn(res: *mut decNumber,
                   rhs: *const decNumber,
                   ctx: *mut Context)
                   -> *mut decNumber;
    fn decNumberLog10(res: *mut decNumber,
                      rhs: *const decNumber,
                      ctx: *mut Context)
                      -> *mut decNumber;
}

#[allow(unused)]
#[cfg(test)]
mod tests {
    #[cfg(any(feature = "ord_subset", feature = "rustc-serialize"))]
    use super::*;
    #[cfg(any(feature = "ord_subset", feature = "serde"))]
    use std::collections::BTreeMap;

    #[cfg(feature = "ord_subset")]
    use ord_subset;

    #[cfg(feature = "rustc-serialize")]
    use rustc_serialize::json;

    #[cfg(feature = "serde")]
    use serde_json::{from_str, to_string};

    use rand::{self, Rng};
    use rand::distributions::{IndependentSample, Range};

    #[allow(unused_imports)]
    use test::{black_box, Bencher};

    #[test]
    fn d128_to_f32_fuzz() {
        assert!(f32::from(d128!(NaN)).is_nan());
        assert!(d128!(Inf).is_infinite());
        assert!(d128!(Inf) > d128::zero());
        let inf = f32::from(d128!(Inf));
        assert!(inf.is_infinite(), "expected inf, val: {}", inf);
    }

    #[test]
    fn test_d128_to_f64_approx() {
        let a = 1.23456789f64;
        assert_relative_eq!(a, f64::from(d128!(1.23456789)), epsilon = 1e-6f64);
        let a = 4000.2340293842;
        assert_relative_eq!(a, f64::from(d128!(4000.2340293842)), epsilon = 1e-6f64);
    }

    #[test]
    fn test_d128_to_f32_approx() {
        let a = 1.23456789f32;
        assert_relative_eq!(a, f32::from(d128!(1.23456789)), epsilon = 1e-6f32);
        let a = 4000.2340293842;
        assert_relative_eq!(a, f32::from(d128!(4000.2340293842)), epsilon = 1e-6f32);
    }

    #[bench]
    fn bench_d128_to_f64_small(b: &mut Bencher) {
        let x = d128!(1.23456789);
        b.iter(|| f64::from(x));
    }

    #[bench]
    fn bench_d128_to_f64_larger(b: &mut Bencher) {
        let x = d128!(4000.2340293842);
        b.iter(|| f64::from(x));
    }

    #[bench]
    fn bench_d128_to_f32_small(b: &mut Bencher) {
        let x = d128!(1.23456789);
        b.iter(|| f32::from(x));
    }

    #[bench]
    fn bench_d128_to_f32_larger(b: &mut Bencher) {
        let x = d128!(4000.2340293842);
        b.iter(|| f32::from(x));
    }

    #[test]
    fn checks_a_u64_conversion_that_failed_somehow() {
        let e: d128 = d128!(100000000);
        let x = d128!(10135);
        assert_eq!(u64::from(e * x), 1013500000000);
        assert_eq!(u64::from(x * e), 1013500000000);
    }

    #[test]
    fn checks_a_u64_potential_edge_case() {
        let e: d128 = d128!(100000000);
        //let e = d128!(1e8);
        //assert_eq!(e, E);
        let x = d128!(0.12345678);
        assert_eq!(u64::from(e * x), 12345678u64);
        //assert_eq!(u64::from(E * x), 12345678u64);
        assert_eq!(u64::from(x * e), 12345678u64);
    }

    #[test]
    fn verifies_u64_from_d128_on_large_number_of_examples() {
        macro_rules! check {
            ($n:expr) => {
                let u: u64 = $n;
                assert_eq!(u64::from(d128!($n)), u);
            }
        }

        check!(0);
        check!(1);
        check!(2);
        check!(3);
        check!(4);
        check!(10);
        check!(100);
        check!(1456789);
        check!(12345678);
        check!(123456789);
        check!(17473551615);
        check!(1744073551615);
        check!(1744073709551615);
        check!(18446744073709551615);
    }

    #[bench]
    fn sums_vec_of_100_000_u64_1e8_of_float(b: &mut Bencher) {
        let x = 0.00012345f64;
        let mut xs: Vec<u64> = Vec::with_capacity(100_000);
        let mut ys: Vec<f64> = Vec::with_capacity(100_000);
        for i in 0..100_000u64 {
            xs.push(((i as f64 * x) * 1e8) as u64);
            ys.push(i as f64 * x);
        }

        assert!(
            xs.iter().sum::<u64>() as f64 / 1e8
            -
            ys.iter().sum::<f64>()
            <
            1e-8
        );

        b.iter(|| {
            xs.iter().sum::<u64>() as f64 / 1e8
        });
    }


    #[cfg(feature = "faster")]
    #[bench]
    fn sums_vec_of_100_000_u64_1e8_of_float_simd(b: &mut Bencher) {
        use faster::*;
        let x = 0.00012345f64;
        let mut xs: Vec<u64> = Vec::with_capacity(100_000);
        let mut ys: Vec<f64> = Vec::with_capacity(100_000);
        for i in 0..100_000u64 {
            xs.push(((i as f64 * x) * 1e8) as u64);
            ys.push(i as f64 * x);
        }

        assert!(
            ((&xs[..]).simd_iter(u64s(0))
                .simd_reduce(u64s(0), |acc, v| acc + v)
                .sum() as f64 / 1e8)
            -
            ys.iter().sum::<f64>()
            <
            1e-8
        );

        b.iter(|| {
            ((&xs[..]).simd_iter(u64s(0))
                .simd_reduce(u64s(0), |acc, v| acc + v)
                .sum() as f64 / 1e8)
        });
    }

    #[cfg(feature = "faster")]
    #[bench]
    fn sums_vec_of_100_000_f32_simd(b: &mut Bencher) {
        use faster::*;
        let x = 0.00012345f32;
        let mut xs: Vec<f32> = Vec::with_capacity(100_000);
        for i in 0..100_000u32 {
            xs.push(i as f32 * x);
        }

        b.iter(|| {
            (&xs[..]).simd_iter(f32s(0.0))
                .simd_reduce(f32s(0.0), |acc, v| acc + v)
                .sum()
        });
    }

    #[bench]
    fn sums_vec_of_100_000_f32(b: &mut Bencher) {
        let x = 0.00012345f32;
        let mut xs: Vec<f32> = Vec::with_capacity(100_000);
        for i in 0..100_000u32 {
            xs.push(i as f32 * x);
        }

        b.iter(|| {
            xs.iter().sum::<f32>()
        });
    }

    #[bench]
    fn sums_vec_of_100_000_f64(b: &mut Bencher) {
        let x = 0.00012345f64;
        let mut xs: Vec<f64> = Vec::with_capacity(100_000);
        for i in 0..100_000u32 {
            xs.push(i as f64 * x);
        }

        b.iter(|| {
            xs.iter().sum::<f64>()
        });
    }

    #[bench]
    fn sums_vec_of_100_000(b: &mut Bencher) {
        let x = d128!(0.00012345);
        let mut xs: Vec<d128> = Vec::with_capacity(100_000);
        for i in 0..100_000u32 {
            xs.push(d128::from(i) * x);
        }

        b.iter(|| {
            xs.iter().sum::<d128>()
        });
    }

    #[test]
    fn it_parses_zero_in_exp_notation() {
        assert_eq!(d128::from_str("0E-8").unwrap(), d128!(0.00000000));
    }

    #[test]
    fn it_verifies_infinity_fns() {
        assert!(d128::infinity().is_infinite());
        assert!(!d128::infinity().is_negative());
        assert!(d128::neg_infinity().is_infinite());
        assert!(d128::neg_infinity().is_negative());
        assert_eq!(d128::infinity() + d128!(1), d128::infinity());
    }

    #[test]
    fn test_sum_impl() {
        let decimals = vec![d128!(1), d128!(2), d128!(3), d128!(4)];
        assert_eq!(d128!(10), decimals.iter().sum());
        assert_eq!(d128!(10), decimals.into_iter().sum());
    }

    #[test]
    fn it_checks_default_is_zero() {
        assert_eq!(d128::default(), d128::zero());
    }

    #[test]
    fn it_handles_a_real_world_small_number_that_landed_in_db_as_nan() {
        let amt = d128!(1E-8);
        let price = d128!(0.00143500);
        let fee = d128!(1E-8);
        let total = d128!(0E-8);
        assert_eq!(d128::zero(), total);
        let as_calculated = (d128!(1) - fee / total).quantize(d128!(0.00000001));
        assert!(as_calculated.is_nan());
        let fixed = (d128!(1) - fee / total.max(d128!(0.00000001))).quantize(d128!(0.00000001));
        assert!(fixed.is_finite());
    }

    #[test]
    fn it_checks_the_max_of_nan_and_a_real_number_is_the_real_number() {
        let x = d128!(NaN);
        assert!(x.is_nan());
        assert_eq!(x.max(d128::zero()), d128::zero());
        assert_eq!(x.max(d128!(-100)), d128!(-100));
    }

    #[bench]
    fn random_number_via_u32_range(b: &mut Bencher) {
        let mut rng = rand::thread_rng();
        let range = Range::new(980_000_000u32, 1_200_000_000u32);
        let e = d128!(1_000_000_000);
        b.iter(|| {
            let d: d128 = d128::from(range.ind_sample(&mut rng)) / e;
            d
        });
    }

    #[test]
    fn it_validates_range_of_random_number_via_u32_range() {
        let mut rng = rand::thread_rng();
        let range = Range::new(980_000_000u32, 1_200_000_000u32);
        let e = d128!(1_000_000_000);
        let d: d128 = d128::from(range.ind_sample(&mut rng)) / e;
        println!("d={}", d);
        assert!(d >= d128!(0.98));
        assert!(d <= d128!(1.2));
    }

    #[bench]
    fn random_number_via_u32(b: &mut Bencher) {
        let mut rng = rand::thread_rng();
        b.iter(|| {
            let d: d128 = rng.gen::<u32>().into();
            d
        });
    }

    #[bench]
    fn random_number_via_u64(b: &mut Bencher) {
        let mut rng = rand::thread_rng();
        b.iter(|| {
            let d: d128 = rng.gen::<u64>().into();
            d
        });
    }

    #[test]
    fn test_deref_does_not_blow_the_machine_up() {
        fn add(a: &d128, b: &d128) -> d128 {
            *a + *b
        }
        let a = d128!(1);
        let b = d128!(1);
        let c = add(&a, &b);
        assert_eq!(c, d128!(2));
    }

    #[test]
    fn test_deref_mutate() {
        let a = &mut d128!(1.011);
        *a += d128!(1.022);
        assert_eq!(a, &d128!(2.033));
    }

    #[test]
    fn default() {
        assert_eq!(d128::zero(), d128::default());
        assert_eq!(d128::zero(), Default::default());
    }

    #[test]
    fn special() {
        assert!(d128::infinity().is_infinite());
        assert!(!d128::infinity().is_negative());

        assert!(d128::neg_infinity().is_infinite());
        assert!(d128::neg_infinity().is_negative());

        assert_eq!(d128::infinity() + d128!(1), d128::infinity());
    }

    #[cfg(feature = "ord_subset")]
    #[test]
    #[should_panic]
    fn test_ord_subset_nan() {
        ord_subset::OrdVar::new(d128!(NaN));
    }

    #[cfg(feature = "ord_subset")]
    #[test]
    #[should_panic]
    fn test_ord_subset_qnan() {
        ord_subset::OrdVar::new(d128!(qNaN));
    }

    #[cfg(feature = "ord_subset")]
    #[test]
    fn test_ord_subset_zero() {
        assert_eq!(*ord_subset::OrdVar::new(d128::zero()), d128::zero());
    }

    #[cfg(feature = "ord_subset")]
    #[test]
    fn test_into_for_btreemap() {
        let mut m = BTreeMap::<ord_subset::OrdVar<d128>, i64>::new();
        m.insert(d128!(1.1).into(), 1);
        assert_eq!(m[&d128!(1.1).into()], 1);
    }

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

    #[cfg(feature = "serde")]
    #[test]
    fn test_serde() {
        let mut a = BTreeMap::new();
        a.insert("price".to_string(), d128!(432.232));
        a.insert("amt".to_string(), d128!(9.9));
        assert_eq!(&to_string(&a).unwrap(),
            "{\"amt\":\"9.9\",\"price\":\"432.232\"}");
        let b = from_str("{\"price\":\"432.232\",\"amt\":\"9.9\"}").unwrap();
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
        assert_eq!(d128!(5) << 2, d128!(500));
        assert_eq!(d128!(500) >> 1, d128!(50));
    }

    #[test]
    fn assign_op() {
        let mut x = d128!(1);
        x += d128!(2);
        assert_eq!(x, d128!(3));
        x *= d128!(3);
        assert_eq!(x, d128!(9));
        x -= d128!(1);
        assert_eq!(x, d128!(8));
        x /= d128!(16);
        assert_eq!(x, d128!(0.5));
        x <<= 2;
        assert_eq!(x, d128!(50));
        x >>= 1;
        assert_eq!(x, d128!(5));
    }

    #[test]
    fn as_ref_operand() {
        assert_eq!(d128!(1.1), d128!(1.1).min(d128!(2.2)));
        assert_eq!(d128!(1.1), d128!(1.1).min(&d128!(2.2)));
    }

    #[test]
    fn from_i64() {
        assert_eq!(d128::from_str(&::std::i64::MAX.to_string()).unwrap(),
                   d128::from(::std::i64::MAX));
        assert_eq!(d128::from(0i32), d128::from(0i64));
        assert_eq!(d128::from_str(&(::std::i64::MIN).to_string()).unwrap(),
                   d128::from(::std::i64::MIN));
    }

    #[test]
    fn from_u64() {
        assert_eq!(d128::from_str(&::std::u64::MAX.to_string()).unwrap(),
                   d128::from(::std::u64::MAX));
        assert_eq!(d128::from(0i32), d128::from(0u64));
        assert_eq!(d128::from_str(&(::std::u64::MIN).to_string()).unwrap(),
                   d128::from(::std::u64::MIN));
    }

    #[test]
    fn test_sum() {
        let decimals = vec![d128!(1), d128!(2), d128!(3), d128!(4)];

        assert_eq!(d128!(10), decimals.iter().sum());

        assert_eq!(d128!(10), decimals.into_iter().sum());
    }
}
