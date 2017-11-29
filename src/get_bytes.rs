extern crate decimal; 
extern crate clap;
use std::str::FromStr;

fn main() {
    let args: clap::ArgMatches = clap::App::new("bytes")
        .version("0.1")
        .arg(clap::Arg::with_name("dec_literal")
             .help("Decimal float literal to show bytes for")
             .required(true))
        .arg(clap::Arg::with_name("f64")
             .help("Show bytes for the f64 representation of the number, instead of d128")
             .short("d")
             .long("f64")
             .alias("double")
             .alias("float64"))
        .arg(clap::Arg::with_name("f32")
             .help("Show bytes for the f32 representation of the number, instead of d128")
             .short("f")
             .long("f32")
             .alias("float")
             .alias("float32"))
        .get_matches();

    let literal = args.value_of("dec_literal").unwrap();

    if args.is_present("f64") {
        let f = f64::from_str(&literal).expect("Invalid float literal");
        println!("Bytes for {} (f64)", f);
        println!("{:?}", unsafe { ::std::mem::transmute::<f64, [u8; 8]>(f) });
    } else if args.is_present("f32") {
        let f = f32::from_str(&literal).expect("Invalid float literal");
        println!("Bytes for {} (f32)", f);
        println!("{:?}", unsafe { ::std::mem::transmute::<f32, [u8; 4]>(f) });
    } else {
        let d = decimal::d128::from_str(&literal).expect("Invalid float literal");
        println!("Bytes for {}", d);
        println!("{:?}", d.to_raw_bytes());
    }
}
