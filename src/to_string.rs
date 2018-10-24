extern crate decimal; 
extern crate clap;
use std::str::FromStr;

fn main() {
    let args: clap::ArgMatches = clap::App::new("to-string")
        .version("0.1")
        .arg(clap::Arg::with_name("precision")
             .short("r")
             .long("round")
             .takes_value(true)
             .required(false)
             .help("round to <precision>"))
        .arg(clap::Arg::with_name("decimal-literal")
             .help("Decimal float literal to show string for")
             .required(true))
        .get_matches();

    let literal = args.value_of("decimal-literal").unwrap();

    let mut d = decimal::d128::from_str(&literal).expect("Invalid float literal");

    if let Some(q) = args.value_of("precision") {
        let q = decimal::d128::from_str(q).expect("failed to parse --round argument");
        assert!(q.is_finite(), "parsed --round argument is not finite: {}", q);
        d = d.round(q);
    }

    println!("{}", d);
}
