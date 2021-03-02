extern crate decimal;

use decimal::*;
use std::fmt;
use std::fs::File;
use std::path::Path;
use std::io::BufRead;
use std::io::BufReader;

fn find_end_quote(s: &str, quote: char) -> Option<usize> {
    match s.find(quote) {
        None => None,
        Some(i) => {
            match s[i + 1..].chars().next() {
                None => Some(i),
                Some(c) if c == quote => {
                    find_end_quote(&s[i + 2..], quote).and_then(|j| Some(i + 2 + j))
                }
                Some(_) => Some(i),
            }
        }
    }
}

fn split_token<'a>(line: &'a str) -> (&'a str, &'a str) {
    let line = line.trim_start();
    if line.starts_with("--") {
        ("", "")
    } else if line.starts_with("\"") {
        let end = find_end_quote(&line[1..], '"').expect("Unmatched double quote") + 1;
        (&line[1..end], &line[end + 1..])
    } else if line.starts_with("'") {
        let end = find_end_quote(&line[1..], '\'').expect("Unmatched single quote") + 1;
        (&line[1..end], &line[end + 1..])
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
    CopySign(&'a str, &'a str),
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
    Plus(&'a str),
    Power(&'a str, &'a str),
    Quantize(&'a str, &'a str),
    Reduce(&'a str),
    Remainder(&'a str, &'a str),
    RemainderNear(&'a str, &'a str),
    Rescale(&'a str, &'a str),
    Rotate(&'a str, &'a str),
    SameQuantum(&'a str, &'a str),
    ScaleB(&'a str, &'a str),
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
    raw: &'a str,
    id: &'a str,
    op: Op<'a>,
    expected_value: &'a str,
    expected_status: Status,
}

#[derive(Debug)]
enum Instr<'a> {
    Directive(Directive<'a>),
    Test(Test<'a>),
}

fn parse_directive<'a>(s: &mut Scanner<'a>) -> Directive<'a> {
    let keyword = s.current().trim_end_matches(':').to_lowercase();
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
                       .trim_start_matches('+')
                       .parse::<isize>()
                       .expect("No value for maxexponent");
            Directive::MaxExponent(val)
        }
        "minexponent" => {
            let val = s.next().parse::<isize>().expect("No value for minexponent");
            Directive::MinExponent(val)
        }
        "version" => Directive::Version(s.next()),
        "extended" => {
            let val = s.next().parse::<isize>().expect("No value for extended");
            Directive::Extended(val != 0)
        }
        "clamp" => {
            let val = s.next().parse::<isize>().expect("No value for clamp");
            Directive::Clamp(val != 0)
        }
        "dectest" => Directive::Test(s.next()),
        _ => panic!("Cannot parse directive {} {}", keyword, s.remaining()),
    }
}

fn parse_test<'a>(raw: &'a str, s: &mut Scanner<'a>) -> Test<'a> {
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
        "comparetotmag" => Op::CompareTotalMag(s.next(), s.next()),
        "copy" => Op::Copy(s.next()),
        "copyabs" => Op::CopyAbs(s.next()),
        "copynegate" => Op::CopyNegate(s.next()),
        "copysign" => Op::CopySign(s.next(), s.next()),
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
        "plus" => Op::Plus(s.next()),
        "power" => Op::Power(s.next(), s.next()),
        "quantize" => Op::Quantize(s.next(), s.next()),
        "reduce" => Op::Reduce(s.next()),
        "remainder" => Op::Remainder(s.next(), s.next()),
        "remaindernear" => Op::RemainderNear(s.next(), s.next()),
        "rescale" => Op::Rescale(s.next(), s.next()),
        "rotate" => Op::Rotate(s.next(), s.next()),
        "samequantum" => Op::SameQuantum(s.next(), s.next()),
        "scaleb" => Op::ScaleB(s.next(), s.next()),
        "shift" => Op::Shift(s.next(), s.next()),
        "squareroot" => Op::SquareRoot(s.next()),
        "subtract" => Op::Subtract(s.next(), s.next()),
        "toeng" => Op::ToEng(s.next()),
        "tointegral" => Op::ToIntegral(s.next()),
        "tointegralx" => Op::ToIntegralExact(s.next()),
        "tosci" => Op::ToSci(s.next()),
        "trim" => Op::Trim(s.next()),
        "xor" => Op::Xor(s.next(), s.next()),
        err => panic!("Unknown op {}", err),
    };
    if s.next() != "->" {
        panic!("Missing -> [{} {}]", s.current(), s.remaining());
    }
    let value = s.next();
    let mut status = Status::empty();
    loop {
        let cond = s.next().to_lowercase();
        if cond.is_empty() {
            break;
        }
        // We only support IEEE flags.
        status = status |
                 match cond.as_ref() {
            "conversion_syntax" => Status::CONVERSION_SYNTAX,
            "division_by_zero" => Status::DIVISION_BY_ZERO,
            "division_impossible" => Status::DIVISION_IMPOSSIBLE,
            "division_undefined" => Status::DIVISION_UNDEFINED,
            "insufficient_storage" => Status::empty(), // INSUFFICIENT_STORAGE,
            "inexact" => Status::INEXACT,
            "invalid_context" => Status::empty(), // INVALID_CONTEXT,
            "invalid_operation" => Status::INVALID_OPERATION,
            "lost_digits" => Status::empty(), // LOST_DIGITS,
            "overflow" => Status::OVERFLOW,
            "clamped" => Status::empty(), // CLAMPED,
            "rounded" => Status::empty(), // ROUNDED,
            "subnormal" => Status::empty(), // SUBNORMAL,
            "underflow" => Status::UNDERFLOW,
            _ => panic!("Cannot parse condition {}", s.current()),
        }
    }
    Test {
        raw: raw,
        id: id,
        op: op,
        expected_value: value,
        expected_status: status,
    }
}

fn parse_line<'a>(line: &'a str) -> Option<Instr<'a>> {
    let mut scanner = Scanner::new(line);
    match scanner.next() {
        "" => None,
        token if token.starts_with("--") => None,
        token if token.ends_with(":") => Some(Instr::Directive(parse_directive(&mut scanner))),
        _ => Some(Instr::Test(parse_test(line, &mut scanner))),
    }
}

#[derive(PartialEq)]
struct Environment {
    precision: Option<isize>,
    rounding: Option<Rounding>,
    max_exponent: Option<isize>,
    min_exponent: Option<isize>,
    extended: bool,
    clamp: bool,
}

impl Environment {
    fn new() -> Environment {
        Environment {
            precision: None,
            rounding: None,
            max_exponent: None,
            min_exponent: None,
            extended: true,
            clamp: false,
        }
    }

    fn process_directive<'a>(&mut self, path: &Path, directive: Directive<'a>) {
        match directive {
            Directive::Precision(val) => self.precision = Some(val),
            Directive::Rounding(val) => self.rounding = Some(val),
            Directive::MaxExponent(val) => self.max_exponent = Some(val),
            Directive::MinExponent(val) => self.min_exponent = Some(val),
            Directive::Extended(val) => self.extended = val,
            Directive::Clamp(val) => self.clamp = val,
            Directive::Version(_) => {}
            Directive::Test(val) => {
                let path = path.with_file_name(val).with_extension("decTest");
                read_test(&path);
            }
        }
    }
}

#[derive(Default)]
struct TestSummary {
    passed: usize,
    failed: usize,
    ignored: usize,
}

impl TestSummary {
    fn new() -> TestSummary {
        TestSummary::default()
    }

    fn add<'a>(&mut self, result: &'a TestResult) {
        match *result {
            TestResult::Pass(..) => self.passed += 1,
            TestResult::Fail(..) => self.failed += 1,
            TestResult::Ignored(..) => self.ignored += 1,
        };
    }
}

fn read_test(path: &Path) {
    let mut env = Environment::new();
    let mut summary = TestSummary::new();

    for line in BufReader::new(File::open(path).unwrap()).lines() {
        let line = line.unwrap();
        if let Some(instr) = parse_line(&line) {
            match instr {
                Instr::Directive(directive) => {
                    env.process_directive(path, directive);
                }
                Instr::Test(test) => {
                    let result = run_test(&env, test);
                    summary.add(&result);
                    println!("{}", result);
                }
            }
        }
    }
    let id = path.file_stem().unwrap().to_str().unwrap();
    println!("*** {:<20} PASSED: {:>5} FAILED: {:>5} IGNORED: {:>5}\n",
             id,
             summary.passed,
             summary.failed,
             summary.ignored);
}

enum TestResult<'a> {
    Pass(Test<'a>),
    Fail(Test<'a>, String, Status),
    Ignored(Test<'a>),
}

impl<'a> fmt::Display for TestResult<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TestResult::Pass(ref test) => {
                write!(fmt, "[   PASS  ] {}", test.raw)?;
            }
            TestResult::Fail(ref test, ref actual, ref status) => {
                let exp_flags = format!("{:?}", test.expected_status);
                let act_flags = format!("{:?}", status);
                write!(fmt, "[   FAIL  ] {}\n", test.raw)?;
                write!(fmt,
                            "\tEXPECTED: {:<43} {:<43}\n",
                            test.expected_value,
                            exp_flags)?;
                write!(fmt, "\t  ACTUAL: {:<43} {:<43}", actual, act_flags)?;
            }
            TestResult::Ignored(ref test) => {
                write!(fmt, "[ IGNORED ] {}", test.raw)?;
            }
        }
        Ok(())
    }
}

fn parse_operand(s: &str) -> d128 {
    if s.chars().nth(0) == Some('#') {
        d128::from_hex(&s[1..])
    } else {
        use std::str::FromStr;
        d128::from_str(s).expect("Invalid decimal")
    }
}

fn format_result<'a>(value: d128, test: &Test<'a>) -> String {
    if test.expected_value.chars().nth(0) == Some('#') {
        format!("#{:x}", value)
    } else if let Op::ToEng(..) = test.op {
        format!("{:e}", value)
    } else {
        format!("{}", value)
    }
}

macro_rules! simple_op {
    ($test:ident, $res:ident = $func:ident($($arg:ident),+)) => {
        {
            $(
                if $arg == "#" { return TestResult::Ignored($test); }
                let $arg = parse_operand($arg);
            )+
            $res = format_result(d128::$func($($arg),+), &$test);
        }
    };
}

fn run_test<'a>(env: &Environment, test: Test<'a>) -> TestResult<'a> {
    use std::ops::*;

    let d128_env = Environment {
        precision: Some(34),
        rounding: Some(Rounding::HalfEven),
        max_exponent: Some(6144),
        min_exponent: Some(-6143),
        extended: true,
        clamp: true,
    };

    if *env != d128_env {
        return TestResult::Ignored(test);
    }

    let value: String;
    let status: Status;
    d128::set_status(Status::empty());
    match test.op {
        Op::Abs(a) => simple_op!(test, value = abs(a)),
        Op::Add(a, b) => simple_op!(test, value = add(a, b)),
        Op::And(a, b) => simple_op!(test, value = bitand(a, b)),
        Op::Apply(a) => {
            if a == "#" {
                return TestResult::Ignored(test);
            }
            value = format_result(parse_operand(a), &test);
        }
        Op::Canonical(a) => simple_op!(test, value = canonical(a)),
        Op::Compare(a, b) => {
            if a == "#" || b == "#" {
                return TestResult::Ignored(test);
            }
            value = format_result(d128::compare(&parse_operand(a), &parse_operand(b)), &test);
        }
        Op::CompareTotal(a, b) => {
            if a == "#" || b == "#" {
                return TestResult::Ignored(test);
            }
            value = format_result(d128::compare_total(&parse_operand(a), &parse_operand(b)),
                                  &test);
        }
        Op::Divide(a, b) => simple_op!(test, value = div(a, b)),
        Op::Fma(a, b, c) => simple_op!(test, value = mul_add(a, b, c)),
        Op::Invert(a) => simple_op!(test, value = not(a)),
        Op::LogB(a) => simple_op!(test, value = logb(a)),
        Op::Max(a, b) => simple_op!(test, value = max(a, b)),
        Op::Min(a, b) => simple_op!(test, value = min(a, b)),
        Op::Minus(a) => simple_op!(test, value = neg(a)),
        Op::Multiply(a, b) => simple_op!(test, value = mul(a, b)),
        Op::NextMinus(a) => simple_op!(test, value = previous(a)),
        Op::NextPlus(a) => simple_op!(test, value = next(a)),
        Op::NextToward(a, b) => simple_op!(test, value = towards(a, b)),
        Op::Or(a, b) => simple_op!(test, value = bitor(a, b)),
        Op::Power(a, b) => simple_op!(test, value = pow(a, b)),
        Op::Quantize(a, b) => simple_op!(test, value = quantize(a, b)),
        Op::Reduce(a) => simple_op!(test, value = reduce(a)),
        Op::Remainder(a, b) => simple_op!(test, value = rem(a, b)),
        Op::Rotate(a, b) => simple_op!(test, value = rotate(a, b)),
        Op::ScaleB(a, b) => simple_op!(test, value = scaleb(a, b)),
        Op::Subtract(a, b) => simple_op!(test, value = sub(a, b)),
        Op::ToEng(a) => {
            if a == "#" {
                return TestResult::Ignored(test);
            }
            value = format_result(parse_operand(a), &test);
        }
        Op::ToSci(a) => {
            if a == "#" {
                return TestResult::Ignored(test);
            }
            value = format_result(parse_operand(a), &test);
        }
        Op::Xor(a, b) => simple_op!(test, value = bitxor(a, b)),
        _ => {
            return TestResult::Ignored(test);
        }
    }
    status = d128::get_status();
    if value == test.expected_value && status == test.expected_status {
        TestResult::Pass(test)
    } else {
        TestResult::Fail(test, value, status)
    }
}

fn main() {
    let filepath = std::env::args().nth(1).expect("Filename to test");
    let path = Path::new(&filepath);
    read_test(path);
}
