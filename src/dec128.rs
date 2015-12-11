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
// decQuad
pub struct d128 {
    bytes: [uint8_t; 16],
}

impl From<i32> for d128 {
    fn from(val: i32) -> d128 {
        unsafe {
            let mut res: d128 = uninitialized();
            decQuadFromInt32(&mut res, val);
            res
        }
    }
}

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

impl Into<i32> for d128 {
    fn into(self) -> i32 {
        Self::with_context(|ctx| unsafe { decQuadToInt32(&self, ctx, ctx.rounding) })
    }
}

impl Into<u32> for d128 {
    fn into(self) -> u32 {
        Self::with_context(|ctx| unsafe { decQuadToUInt32(&self, ctx, ctx.rounding) })
    }
}

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

impl<'a> BitAnd<&'a d128> for d128 {
    type Output = d128;

    fn bitand(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadAnd(&mut self, &self, other, ctx) };
            self
        })
    }
}

impl<'a> BitOr<&'a d128> for d128 {
    type Output = d128;

    fn bitor(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadOr(&mut self, &self, other, ctx) };
            self
        })
    }
}

impl<'a> BitXor<&'a d128> for d128 {
    type Output = d128;

    fn bitxor(mut self, other: &'a d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadXor(&mut self, &self, other, ctx) };
            self
        })
    }
}

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

    pub fn get_status() -> Status {
        Self::with_context(|ctx| Status::from_bits_truncate(ctx.status))
    }

    pub fn set_status(status: Status) {
        Self::with_context(|ctx| ctx.status = status.bits());
    }

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
    pub fn zero() -> d128 {
        unsafe {
            let mut res = uninitialized();
            decQuadZero(&mut res);
            res
        }
    }

    // Computational.
    pub fn abs(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadAbs(&mut self, &self, ctx) };
            self
        })
    }

    pub fn mul_add<'a, 'b>(mut self, a: &'a d128, b: &'b d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadFMA(&mut self, &self, a, b, ctx) };
            self
        })
    }

    pub fn logb(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadLogB(&mut self, &self, ctx) };
            self
        })
    }

    pub fn max(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadMax(&mut self, &self, other, ctx) };
            self
        })
    }

    pub fn min(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadMin(&mut self, &self, other, ctx) };
            self
        })
    }

    pub fn next(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadNextPlus(&mut self, &self, ctx) };
            self
        })
    }

    pub fn previous(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadNextMinus(&mut self, &self, ctx) };
            self
        })
    }

    pub fn towards(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadNextToward(&mut self, &self, other, ctx) };
            self
        })
    }

    pub fn quantize<'a>(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadQuantize(&mut self, &self, other, ctx) };
            self
        })
    }

    pub fn reduce(mut self) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadReduce(&mut self, &self, ctx) };
            self
        })
    }

    pub fn rotate(mut self, amount: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadRotate(&mut self, &self, amount, ctx) };
            self
        })
    }

    pub fn scaleb(mut self, other: &d128) -> d128 {
        Self::with_context(|ctx| {
            unsafe { decQuadScaleB(&mut self, &self, other, ctx) };
            self
        })
    }

    // Comparisons.
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
    pub fn canonical(mut self) -> d128 {
        unsafe { decQuadCanonical(&mut self, &self) };
        self
    }

    // Non-computational.
    pub fn class(&self) -> Class {
        unsafe { decQuadClass(self) }
    }

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

    pub fn digits(&self) -> u32 {
        unsafe { decQuadDigits(self) }
    }

    pub fn is_canonical(&self) -> bool {
        unsafe { decQuadIsCanonical(self) != 0 }
    }

    pub fn is_finite(&self) -> bool {
        unsafe { decQuadIsFinite(self) != 0 }
    }

    pub fn is_integer(&self) -> bool {
        unsafe { decQuadIsInteger(self) != 0 }
    }

    pub fn is_logical(&self) -> bool {
        unsafe { decQuadIsLogical(self) != 0 }
    }

    pub fn is_infinite(&self) -> bool {
        unsafe { decQuadIsInfinite(self) != 0 }
    }

    pub fn is_nan(&self) -> bool {
        unsafe { decQuadIsNaN(self) != 0 }
    }

    pub fn is_negative(&self) -> bool {
        unsafe { decQuadIsNegative(self) != 0 }
    }

    pub fn is_normal(&self) -> bool {
        unsafe { decQuadIsNormal(self) != 0 }
    }

    pub fn is_positive(&self) -> bool {
        unsafe { decQuadIsPositive(self) != 0 }
    }

    pub fn is_signaling(&self) -> bool {
        unsafe { decQuadIsSignaling(self) != 0 }
    }

    pub fn is_signed(&self) -> bool {
        unsafe { decQuadIsSigned(self) != 0 }
    }

    pub fn is_subnormal(&self) -> bool {
        unsafe { decQuadIsSubnormal(self) != 0 }
    }

    pub fn is_zero(&self) -> bool {
        unsafe { decQuadIsZero(self) != 0 }
    }
}

#[link(name = "decNumber")]
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
