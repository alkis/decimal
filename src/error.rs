quick_error! {
    #[derive(Debug)]
    pub enum Error {
        Conversion {
            display("Invalid floating point number")
        }
        Overflow {
            display("Overflow")
        }
        Underflow {
            display("Underflow")
        }
    }
}

pub type Result<T> = ::std::result::Result<T, Error>;
