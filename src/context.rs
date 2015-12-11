use libc::{uint8_t, int32_t, uint32_t};
use std::fmt;
use super::Rounding;
use super::Status;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Context {
    digits: int32_t,
    emax: int32_t,
    emin: int32_t,
    pub rounding: Rounding,
    traps: uint32_t,
    pub status: uint32_t,
    clamp: uint8_t,
}

impl fmt::Display for Context {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt,
               "digits: {} exp: [{}, {}] rounding: {:?} status: {:?} clamp: {}",
               self.digits,
               self.emin,
               self.emax,
               self.rounding,
               Status::from_bits_truncate(self.status),
               self.clamp == 1)
    }
}
