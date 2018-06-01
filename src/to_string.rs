extern crate decimal; 
extern crate clap;
use std::str::FromStr;

fn main() {
    let args: clap::ArgMatches = clap::App::new("to-string")
        .version("0.1")
        .arg(clap::Arg::with_name("dec_literal")
             .help("Decimal float literal to show string for")
             .required(true))
        .get_matches();

    let literal = args.value_of("dec_literal").unwrap();

    let d = decimal::d128::from_str(&literal).expect("Invalid float literal");
    println!("{}", d);
}
