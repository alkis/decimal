extern crate decimal;

use decimal::*;
use std::fs::File;
use std::path::Path;
use std::io::BufRead;
use std::io::BufReader;

/// Splits the line into the first token and the rest of the line.
/// The token can be quoted in single or double quotes and it will be returned without the quotes.
/// When the rest of the line is empty it means the whole line was processed.
///
/// # Example
///
/// ```rust
/// let line = "a '1 2' b";
/// let (token, line) = split_token(line);
/// assert_eq!(token, "a");
/// assert_eq!(line, "'1 2' b");
/// let (token, line) = split_token(line);
/// assert_eq!(token, "1 2");
/// assert_eq!(line, "b");
/// let (token, line) = split_token(line);
/// assert_eq!(token, "b");
/// assert_eq!(line, "");
/// ```
fn split_token<'a>(line: &'a str) -> (&'a str, &'a str) {
    let line = line.trim_left();
    if line.starts_with("--") {
        ("", "")
    } else if line.starts_with("\"") {
        let end = line[1..].find('"').expect("Unmatched double quote");
        (&line[1..end], &line[end + 2..])
    } else if line.starts_with("'") {
        let end = line[1..].find('\'').expect("Unmatched single quote");
        (&line[1..end], &line[end + 2..])
    } else {
        match line.find(char::is_whitespace) {
            None => (line, ""),
            Some(end) => (&line[0..end], &line[end + 1..]),
        }
    }
}

#[derive(Debug)]
struct Scanner<'a> {
    current: &'a str,
    remaining: &'a str,
}

impl<'a> Scanner<'a> {
    pub fn new(line: &'a str) -> Scanner<'a> {
        Scanner {
            current: "",
            remaining: line,
        }
    }

    pub fn current(&self) -> &'a str {
        self.current
    }

    pub fn remaining(&self) -> &'a str {
        self.remaining
    }

    pub fn next(&mut self) -> &'a str {
        let (current, remaining) = split_token(self.remaining);
        self.current = current;
        self.remaining = remaining;
        self.current
    }
}

#[derive(Debug)]
enum Directive<'a> {
    Precision(isize),
    Rounding(Rounding),
    MaxExponent(isize),
    MinExponent(isize),
    Version(&'a str),
    Extended(bool),
    Clamp(bool),
    Test(&'a str),
}

#[derive(Debug)]
enum Op<'a> {
    Abs(&'a str),
    Add(&'a str, &'a str),
    And(&'a str, &'a str),
    Apply(&'a str),
    Canonical(&'a str),
    Class(&'a str),
    Compare(&'a str, &'a str),
    CompareSig(&'a str, &'a str),
    CompareTotal(&'a str, &'a str),
    CompareTotalMag(&'a str, &'a str),
    Copy(&'a str),
    CopyAbs(&'a str),
    CopyNegate(&'a str),
    CopySign(&'a str),
    Divide(&'a str, &'a str),
    DivideInt(&'a str, &'a str),
    Exp(&'a str),
    Fma(&'a str, &'a str, &'a str),
    Invert(&'a str),
    Ln(&'a str),
    Log10(&'a str),
    LogB(&'a str),
    Max(&'a str, &'a str),
    MaxMag(&'a str, &'a str),
    Min(&'a str, &'a str),
    MinMag(&'a str, &'a str),
    Minus(&'a str),
    Multiply(&'a str, &'a str),
    NextMinus(&'a str),
    NextPlus(&'a str),
    NextToward(&'a str, &'a str),
    Or(&'a str, &'a str),
    Plus(&'a str, &'a str),
    Quantize(&'a str, &'a str),
    Reduce(&'a str),
    Remainder(&'a str, &'a str),
    Rescale(&'a str, &'a str),
    Rotate(&'a str, &'a str),
    SameQuantum(&'a str, &'a str),
    ScaleB(&'a str),
    Shift(&'a str, &'a str),
    SquareRoot(&'a str),
    Subtract(&'a str, &'a str),
    ToEng(&'a str),
    ToIntegral(&'a str),
    ToIntegralExact(&'a str),
    ToSci(&'a str),
    Trim(&'a str),
    Xor(&'a str, &'a str),
}

#[derive(Debug)]
struct Test<'a> {
    id: &'a str,
    op: Op<'a>,
    result: &'a str,
    conditions: Status,
}

#[derive(Debug)]
enum Instr<'a> {
    Directive(Directive<'a>),
    Test(Test<'a>),
}

fn parse_directive<'a>(s: &mut Scanner<'a>) -> Directive<'a> {
    let keyword = s.current().trim_right_matches(':').to_lowercase();
    match keyword.as_ref() {
        "precision" => {
            let val = s.next().parse::<isize>().expect("No value for precision");
            Directive::Precision(val)
        }
        "rounding" => {
            Directive::Rounding(match s.next() {
                "ceiling" => Rounding::Ceiling,
                "down" => Rounding::Down,
                "floor" => Rounding::Floor,
                "half_down" => Rounding::HalfDown,
                "half_even" => Rounding::HalfEven,
                "half_up" => Rounding::HalfUp,
                "up" => Rounding::Up,
                "05up" => Rounding::ZeroOrFiveUp,
                err => panic!("Unknown rounding mode {}", err),
            })
        }
        "maxexponent" => {
            let val = s.next()
                       .trim_left_matches('+')
                       .parse::<isize>()
                       .expect("No value for maxexponent");
            Directive::MaxExponent(val)
        }
        "minexponent" => {
            let val = s.next().parse::<isize>().expect("No value for minexponent");
            Directive::MinExponent(val)
        }
        "version" => {
            Directive::Version(s.next())
        }
        "extended" => {
            let val = s.next().parse::<isize>().expect("No value for extended");
            Directive::Extended(val != 0)
        }
        "clamp" => {
            let val = s.next().parse::<isize>().expect("No value for clamp");
            Directive::Clamp(val != 0)
        }
        "dectest" => {
            Directive::Test(s.next())
        }
        _ => panic!("Cannot parse directive {} {}", s.current(), s.remaining()),
    }
}

fn parse_test<'a>(s: &mut Scanner<'a>) -> Test<'a> {
    let id = s.current();
    let op = match s.next().to_lowercase().as_ref() {
        "abs" => Op::Abs(s.next()),
        "add" => Op::Add(s.next(), s.next()),
        "and" => Op::And(s.next(), s.next()),
        "apply" => Op::Apply(s.next()),
        "canonical" => Op::Canonical(s.next()),
        "class" => Op::Class(s.next()),
        "compare" => Op::Compare(s.next(), s.next()),
        "comparesig" => Op::CompareSig(s.next(), s.next()),
        "comparetotal" => Op::CompareTotal(s.next(), s.next()),
        "comparetotalmag" => Op::CompareTotalMag(s.next(), s.next()),
        "copy" => Op::Copy(s.next()),
        "copyabs" => Op::CopyAbs(s.next()),
        "copynegate" => Op::CopyNegate(s.next()),
        "copysign" => Op::CopySign(s.next()),
        "divide" => Op::Divide(s.next(), s.next()),
        "divideint" => Op::DivideInt(s.next(), s.next()),
        "exp" => Op::Exp(s.next()),
        "fma" => Op::Fma(s.next(), s.next(), s.next()),
        "invert" => Op::Invert(s.next()),
        "ln" => Op::Ln(s.next()),
        "log10" => Op::Log10(s.next()),
        "logb" => Op::LogB(s.next()),
        "max" => Op::Max(s.next(), s.next()),
        "maxmag" => Op::MaxMag(s.next(), s.next()),
        "min" => Op::Min(s.next(), s.next()),
        "minmag" => Op::MinMag(s.next(), s.next()),
        "minus" => Op::Minus(s.next()),
        "multiply" => Op::Multiply(s.next(), s.next()),
        "nextminus" => Op::NextMinus(s.next()),
        "nextplus" => Op::NextPlus(s.next()),
        "nexttoward" => Op::NextToward(s.next(), s.next()),
        "or" => Op::Or(s.next(), s.next()),
        "plus" => Op::Plus(s.next(), s.next()),
        "quantize" => Op::Quantize(s.next(), s.next()),
        "reduce" => Op::Reduce(s.next()),
        "remainder" => Op::Remainder(s.next(), s.next()),
        "rescale" => Op::Rescale(s.next(), s.next()),
        "rotate" => Op::Rotate(s.next(), s.next()),
        "samequantum" => Op::SameQuantum(s.next(), s.next()),
        "scaleb" => Op::ScaleB(s.next()),
        "shift" => Op::Shift(s.next(), s.next()),
        "squareroot" => Op::SquareRoot(s.next()),
        "subtract" => Op::Subtract(s.next(), s.next()),
        "toeng" => Op::ToEng(s.next()),
        "tointegral" => Op::ToIntegral(s.next()),
        "tointegralexact" => Op::ToIntegralExact(s.next()),
        "tosci" => Op::ToSci(s.next()),
        "trim" => Op::Trim(s.next()),
        "xor" => Op::Xor(s.next(), s.next()),
        err => panic!("Unknown op {}", err),
    };
    if s.next() != "->" {
        panic!("Missing -> [{} {}]", s.current(), s.remaining());
    }
    let result = s.next();
    let mut status = Status::empty();
    loop {
        let cond = s.next().to_lowercase();
        if cond.is_empty() {
            break;
        }
        status = status |
                 match cond.as_ref() {
            "conversion_syntax" => CONVERSION_SYNTAX,
            "division_by_zero" => DIVISION_BY_ZERO,
            "division_impossible" => DIVISION_IMPOSSIBLE,
            "division_undefined" => DIVISION_UNDEFINED,
            "insufficient_storage" => INSUFFICIENT_STORAGE,
            "inexact" => INEXACT,
            "invalid_context" => INVALID_CONTEXT,
            "invalid_operation" => INVALID_OPERATION,
            "lost_digits" => LOST_DIGITS,
            "overflow" => OVERFLOW,
            "clamped" => CLAMPED,
            "rounded" => ROUNDED,
            "subnormal" => SUBNORMAL,
            "underflow" => UNDERFLOW,
            _ => panic!("Cannot parse condition {}", s.current()),
        }
    }
    Test {
        id: id,
        op: op,
        result: result,
        conditions: status,
    }
}

fn parse_line<'a>(line: &'a str) -> Option<Instr<'a>> {
    let mut scanner = Scanner::new(line);
    match scanner.next() {
        "" => None,
        token if token.starts_with("--") => None,
        token if token.ends_with(":") => Some(Instr::Directive(parse_directive(&mut scanner))),
        _ => Some(Instr::Test(parse_test(&mut scanner))),
    }
}

fn run_test(path: &Path) {
    let file = File::open(path);
    println!("{:?}", file);
    for line in BufReader::new(File::open(path).unwrap()).lines() {
        let line = line.unwrap();
        println!("{}", line);
        println!("\t{:?}", parse_line(&line));
    }
}

fn main() {
    let filepath = std::env::args().nth(1).expect("Filename to test");
    let path = Path::new(&filepath);
    run_test(path);
}
