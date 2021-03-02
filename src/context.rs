use std::fmt;
use super::Rounding;
use super::Status;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Context {
    digits: i32,
    emax: i32,
    emin: i32,
    pub rounding: Rounding,
    traps: u32,
    pub status: u32,
    clamp: u8,
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
