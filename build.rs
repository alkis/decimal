extern crate gcc;

fn main() {
    gcc::Config::new()
        .include("decNumber")
        .file("decNumber/decContext.c")
        .file("decNumber/decDouble.c")
        .file("decNumber/decNumber.c")
        .file("decNumber/decPacked.c")
        .file("decNumber/decQuad.c")
        .file("decNumber/decSingle.c")
        .file("decNumber/decimal128.c")
        .file("decNumber/decimal32.c")
        .file("decNumber/decimal64.c")
        .define("DECNUMDIGITS", Some("34"))
        .compile("libdecNumber.a");
}
