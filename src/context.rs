use libc::{int32_t, uint32_t};

#[repr(C)]
pub enum rounding {
    DEC_ROUND_CEILING = 0,
    DEC_ROUND_UP,
    DEC_ROUND_HALF_UP,
    DEC_ROUND_HALF_EVEN,
    DEC_ROUND_HALF_DOWN,
    DEC_ROUND_DOWN,
    DEC_ROUND_FLOOR,
    DEC_ROUND_05UP,
    DEC_ROUND_MAX,
}

#[repr(C)]
pub struct dCtx {
    digits: int32_t,
    emax: int32_t,
    emin: int32_t,
    round: rounding,
    traps: uint32_t,
    status: uint32_t,
    clamp: uint32_t,
}

#[repr(C)]
#[allow(dead_code)]
pub enum decClass {
    DEC_CLASS_SNAN = 0,
    DEC_CLASS_QNAN,
    DEC_CLASS_NEG_INF,
    DEC_CLASS_NEG_NORMAL,
    DEC_CLASS_NEG_SUBNORMAL,
    DEC_CLASS_NEG_ZERO,
    DEC_CLASS_POS_ZERO,
    DEC_CLASS_POS_SUBNORMAL,
    DEC_CLASS_POS_NORMAL,
    DEC_CLASS_POS_INF,
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
