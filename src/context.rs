use libc::{c_char, int32_t, uint32_t};
use std::fmt;
use std::ffi::CString;
use super::Rounding;
use super::Status;

#[repr(C)]
#[derive(Debug)]
pub struct Context {
    digits: int32_t,
    emax: int32_t,
    emin: int32_t,
    round: Rounding,
    traps: uint32_t,
    status: uint32_t,
    clamp: uint32_t,
}

impl Context {
    pub fn clear_status(&mut self, status: Status) {
        unsafe { decContextClearStatus(self, status.bits()) };
    }

    pub fn status(&mut self) -> Status {
        Status::from_bits(unsafe { decContextGetStatus(self) }).unwrap()
    }

    pub fn save_status(&mut self, mask: Status) -> Status {
        Status::from_bits(unsafe { decContextSaveStatus(self, mask.bits()) }).unwrap()
    }

    pub fn restore_status(&mut self, status: Status, mask: Status) {
        unsafe { decContextRestoreStatus(self, status.bits(), mask.bits()) };
    }

    pub fn set_status(&mut self, status: Status) {
        unsafe { decContextSetStatus(self, status.bits()) };
    }

    pub fn zero_status(&mut self) {
        unsafe { decContextZeroStatus(self) };
    }
}

impl fmt::Display for Context {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        unsafe {
            let cstr = CString::from_raw(decContextStatusToString(self) as *mut c_char);
            fmt.write_str(cstr.to_str().unwrap())
        }
    }
}

#[link(name = "decNumber")]
extern {
    // Context.
    fn decContextClearStatus(ctx: *mut Context, status: uint32_t) -> *mut Context;
    fn decContextGetStatus(ctx: *mut Context) -> uint32_t;
    fn decContextRestoreStatus(ctx: *mut Context,
                               status: uint32_t,
                               mask: uint32_t)
                               -> *mut Context;
    fn decContextSaveStatus(ctx: *mut Context, mask: uint32_t) -> uint32_t;
    fn decContextSetStatus(ctx: *mut Context, status: uint32_t) -> *mut Context;
    fn decContextStatusToString(ctx: *const Context) -> *const c_char;
    fn decContextZeroStatus(ctx: *mut Context) -> *mut Context;
}
