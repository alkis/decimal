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

#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Conversion_syntax: u32 = 0x00000001;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Division_by_zero: u32 = 0x00000002;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Division_impossible: u32 = 0x00000004;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Division_undefined: u32 = 0x00000008;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Insufficient_storage: u32 = 0x00000010;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Inexact: u32 = 0x00000020;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Invalid_context: u32 = 0x00000040;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Invalid_operation: u32 = 0x00000080;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Overflow: u32 = 0x00000200;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Clamped: u32 = 0x000000400;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Rounded: u32 = 0x000000800;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Subnormal: u32 = 0x00001000;
#[allow(non_upper_case_globals,dead_code)]
pub const DEC_Underflow: u32 = 0x00002000;
