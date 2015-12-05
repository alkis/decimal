use context::*;
use error;
use libc::{c_char, int32_t, uint8_t, uint32_t};
use std::cell::RefCell;
use std::ffi::CString;
use std::fmt;
use std::mem::uninitialized;
use std::ops::{Add, Sub, Mul, Div, Rem, Neg, BitAnd, BitOr, BitXor, Not, Shl, Shr};
use std::str::FromStr;
use std::num::FpCategory;

thread_local!(static CTX: RefCell<dCtx> = RefCell::new(d128::ctx()));

#[repr(C)]
#[derive(Copy, Clone)]
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
        unsafe {
            let mut res: d128 = uninitialized();
            decQuadFromUInt32(&mut res, val);
            res
        }
    }
}

impl FromStr for d128 {
    type Err = error::Error;
    fn from_str(s: &str) -> error::Result<Self> {
        match CString::new(s) {
            Err(_) => Err(error::Error::Conversion),
            Ok(cstr) => {
                unsafe {
                    let mut res: d128 = uninitialized();
                    CTX.with(|ctx| {
                        let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                        decContextZeroStatus(ctx);
                        decQuadFromString(&mut res, cstr.into_raw(), ctx);
                        let status = Status::from_bits(decContextGetStatus(ctx)).unwrap();
                        if status.intersects(CONVERSION_SYNTAX) {
                            Err(error::Error::Conversion)
                        } else if status.intersects(OVERFLOW) {
                            Err(error::Error::Overflow)
                        } else if status.intersects(UNDERFLOW) {
                            Err(error::Error::Underflow)
                        } else {
                            Ok(res)
                        }
                    })
                }
            }
        }
    }
}

impl fmt::Display for d128 {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = [0 as i8; 43];
        unsafe {
            decQuadToString(self, buf.as_mut().as_mut_ptr());
            let cstr = CString::from_raw(buf.as_mut().as_mut_ptr());
            fmt.write_str(cstr.to_str().unwrap())
        }
    }
}

impl PartialEq<d128> for d128 {
    fn eq(&self, other: &d128) -> bool {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                let mut res: d128 = uninitialized();
                decQuadCompare(&mut res, self, other, ctx);
                res.is_zero()
            })
        }
    }
}

impl PartialOrd<d128> for d128 {
    fn partial_cmp(&self, other: &d128) -> Option<::std::cmp::Ordering> {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                let mut res: d128 = uninitialized();
                decQuadCompare(&mut res, self, other, ctx);
                if res.is_nan() {
                    None
                } else if res.is_zero() {
                    Some(::std::cmp::Ordering::Equal)
                } else if res.is_positive() {
                    Some(::std::cmp::Ordering::Greater)
                } else if res.is_negative() {
                    Some(::std::cmp::Ordering::Less)
                } else {
                    unreachable!()
                }
            })
        }
    }
}

impl<'a> Add<&'a d128> for d128 {
    type Output = d128;

    fn add(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadAdd(&mut self, &self, other, ctx);
                self
            })
        }
    }
}

impl<'a> Sub<&'a d128> for d128 {
    type Output = d128;

    fn sub(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadSubtract(&mut self, &self, other, ctx);
                self
            })
        }
    }
}

impl<'a> Mul<&'a d128> for d128 {
    type Output = d128;

    fn mul(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadMultiply(&mut self, &self, other, ctx);
                self
            })
        }
    }
}

impl<'a> Div<&'a d128> for d128 {
    type Output = d128;

    fn div(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadDivide(&mut self, &self, other, ctx);
                self
            })
        }
    }
}

impl<'a> Rem<&'a d128> for d128 {
    type Output = d128;

    fn rem(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadRemainder(&mut self, &self, other, ctx);
                self
            })
        }
    }
}

impl Neg for d128 {
    type Output = d128;

    fn neg(mut self) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadMinus(&mut self, &self, ctx);
                self
            })
        }
    }
}

impl<'a> BitAnd<&'a d128> for d128 {
    type Output = d128;

    fn bitand(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadAnd(&mut self, &self, other, ctx);
                self
            })
        }
    }
}

impl<'a> BitOr<&'a d128> for d128 {
    type Output = d128;

    fn bitor(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadOr(&mut self, &self, other, ctx);
                self
            })
        }
    }
}

impl<'a> BitXor<&'a d128> for d128 {
    type Output = d128;

    fn bitxor(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadXor(&mut self, &self, other, ctx);
                self
            })
        }
    }
}

impl Shl<usize> for d128 {
    type Output = d128;

    fn shl(mut self, amount: usize) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                let shift = d128::from(amount as u32);
                decQuadShift(&mut self, &self, &shift, ctx);
                self
            })
        }
    }
}

impl Shr<usize> for d128 {
    type Output = d128;

    fn shr(mut self, amount: usize) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                let shift = -d128::from(amount as u32);
                decQuadShift(&mut self, &self, &shift, ctx);
                self
            })
        }
    }
}

impl Not for d128 {
    type Output = d128;

    fn not(mut self) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadInvert(&mut self, &self, ctx);
                self
            })
        }
    }
}

impl d128 {
    fn ctx() -> dCtx {
        unsafe {
            let mut res: dCtx = uninitialized();
            decContextDefault(&mut res, 128);
            res
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
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadAbs(&mut self, &self, ctx);
                self
            })
        }
    }

    pub fn mul_add<'a, 'b>(mut self, a: &'a d128, b: &'b d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadFMA(&mut self, &self, a, b, ctx);
                self
            })
        }
    }

    pub fn logb(mut self) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadLogB(&mut self, &self, ctx);
                self
            })
        }
    }

    pub fn max<'a>(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadMax(&mut self, &self, other, ctx);
                self
            })
        }
    }

    pub fn min<'a>(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadMin(&mut self, &self, other, ctx);
                self
            })
        }
    }

    pub fn next(mut self) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadNextPlus(&mut self, &self, ctx);
                self
            })
        }
    }

    pub fn previous(mut self) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadNextMinus(&mut self, &self, ctx);
                self
            })
        }
    }

    pub fn towards<'a>(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadNextToward(&mut self, &self, other, ctx);
                self
            })
        }
    }

    pub fn quantize<'a>(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadQuantize(&mut self, &self, other, ctx);
                self
            })
        }
    }

    pub fn reduce(mut self) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadReduce(&mut self, &self, ctx);
                self
            })
        }
    }

    // TODO(alkis): Make amount isize.
    pub fn rotate<'a>(mut self, amount: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadRotate(&mut self, &self, amount, ctx);
                self
            })
        }
    }

    pub fn scaleb<'a>(mut self, other: &'a d128) -> d128 {
        unsafe {
            CTX.with(|ctx| {
                let ctx: &mut dCtx = &mut *ctx.borrow_mut();
                decQuadScaleB(&mut self, &self, other, ctx);
                self
            })
        }
    }

    // Copies.
    pub fn canonical(mut self) -> d128 {
        unsafe {
            decQuadCanonical(&mut self, &self);
            self
        }
    }

    // Non-computational.
    pub fn classify(&self) -> FpCategory {
        use ::std::num::FpCategory::*;
        use context::decClass::*;
        unsafe {
            match decQuadClass(self) {
                DEC_CLASS_QNAN | DEC_CLASS_SNAN => Nan,
                DEC_CLASS_POS_INF | DEC_CLASS_NEG_INF => Infinite,
                DEC_CLASS_POS_ZERO | DEC_CLASS_NEG_ZERO => Zero,
                DEC_CLASS_POS_NORMAL | DEC_CLASS_NEG_NORMAL => Normal,
                DEC_CLASS_POS_SUBNORMAL | DEC_CLASS_NEG_SUBNORMAL => Subnormal,
            }
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
    fn decContextDefault(ctx: *mut dCtx, kind: uint32_t) -> *mut dCtx;
    fn decContextZeroStatus(ctx: *mut dCtx) -> *mut dCtx;
    fn decContextGetStatus(ctx: *mut dCtx) -> uint32_t;
    // Utilities and conversions, extractors, etc.
    fn decQuadFromInt32(res: *mut d128, src: int32_t) -> *mut d128;
    fn decQuadFromString(res: *mut d128, s: *const c_char, ctx: *mut dCtx) -> *mut d128;
    fn decQuadFromUInt32(res: *mut d128, src: uint32_t) -> *mut d128;
    fn decQuadToString(res: *const d128, s: *mut c_char) -> *mut c_char;
    fn decQuadZero(res: *mut d128) -> *mut d128;
    // Computational.
    fn decQuadAbs(res: *mut d128, src: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadAdd(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadAnd(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadDivide(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadFMA(res: *mut d128,
                  a: *const d128,
                  b: *const d128,
                  c: *const d128,
                  ctx: *mut dCtx)
                  -> *mut d128;
    fn decQuadInvert(res: *mut d128, src: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadLogB(res: *mut d128, src: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadMax(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadMin(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadMinus(res: *mut d128, src: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadMultiply(res: *mut d128,
                       a: *const d128,
                       b: *const d128,
                       ctx: *mut dCtx)
                       -> *mut d128;
    fn decQuadNextMinus(res: *mut d128, src: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadNextPlus(res: *mut d128, src: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadNextToward(res: *mut d128,
                         src: *const d128,
                         other: *const d128,
                         ctx: *mut dCtx)
                         -> *mut d128;
    fn decQuadOr(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadQuantize(res: *mut d128,
                       a: *const d128,
                       b: *const d128,
                       ctx: *mut dCtx)
                       -> *mut d128;
    fn decQuadReduce(res: *mut d128, src: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadRemainder(res: *mut d128,
                        a: *const d128,
                        b: *const d128,
                        ctx: *mut dCtx)
                        -> *mut d128;
    fn decQuadRotate(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadScaleB(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadShift(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    fn decQuadSubtract(res: *mut d128,
                       a: *const d128,
                       b: *const d128,
                       ctx: *mut dCtx)
                       -> *mut d128;
    fn decQuadXor(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    // Comparisons.
    fn decQuadCompare(res: *mut d128, a: *const d128, b: *const d128, ctx: *mut dCtx) -> *mut d128;
    // Copies.
    fn decQuadCanonical(res: *mut d128, src: *const d128) -> *mut d128;
    // Non-computational.
    fn decQuadClass(src: *const d128) -> decClass;
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

#[cfg(test)]
mod tests {
    use super::d128;

    #[test]
    fn from_str() {
        use std::str::FromStr;
        assert!(d128::from_str(".1").is_ok());
        assert!(d128::from_str("-.1").is_ok());
        assert!(d128::from_str("0.123456789").is_ok());
        assert!(d128::from_str("-0.123456789").is_ok());
        assert!(d128::from_str("0.1e10").is_ok());
        assert!(d128::from_str("-0.1e10").is_ok());
        assert!(d128::from_str("0.1e-10").is_ok());
        assert!(d128::from_str("-0.1e-10").is_ok());
        assert!(d128::from_str("junk").is_err());
    }
}
