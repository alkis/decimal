use std::iter::once;

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

/// Get a [`TokenStream`] of `compile_error!("message")`
fn error(span: Span, message: &str) -> TokenStream {
    [
        TokenTree::from(Ident::new("compile_error", span)),
        TokenTree::from(Punct::new('!', Spacing::Alone)),
        TokenTree::from(Group::new(
            Delimiter::Parenthesis,
            TokenTree::from(Literal::string(message)).into(),
        )),
    ]
    .into_iter()
    .collect()
}

#[proc_macro]
pub fn d128(args: TokenStream) -> TokenStream {
    let arg = args.to_string();

    // parse argument as d128, error if invalid
    let num = match from_str(&arg) {
        Ok(num) => num,
        Err(s) => {
            return error(Span::call_site(), s);
        }
    };

    // literal array of the parsed value's bytes
    let bytes = num
        .to_raw_bytes()
        .iter()
        .flat_map(|&byte| {
            [
                TokenTree::from(Literal::u8_suffixed(byte)),
                TokenTree::from(Punct::new(',', Spacing::Alone)),
            ]
            .into_iter()
        })
        .collect::<TokenStream>();
    let array = TokenTree::from(Group::new(Delimiter::Bracket, bytes));

    let double_colons = || {
        [
            TokenTree::from(Punct::new(':', Spacing::Joint)),
            TokenTree::from(Punct::new(':', Spacing::Alone)),
        ]
        .into_iter()
    };
    let ident = |s| once(TokenTree::from(Ident::new(s, Span::call_site())));

    // ::decimal::d128::from_raw_bytes(array)
    let mut from_raw_bytes = TokenStream::new();
    from_raw_bytes.extend(double_colons());
    from_raw_bytes.extend(ident("decimal"));
    from_raw_bytes.extend(double_colons());
    from_raw_bytes.extend(ident("d128"));
    from_raw_bytes.extend(double_colons());
    from_raw_bytes.extend(ident("from_raw_bytes"));
    from_raw_bytes.extend(once(TokenTree::from(Group::new(
        Delimiter::Parenthesis,
        array.into(),
    ))));

    // unsafe { from_raw_bytes(...) }
    // TODO: is this correct when host endianness differs from target, or do we
    // need to do a conversion of the bytes in some configurations?
    let mut out = TokenStream::new();
    out.extend(ident("unsafe"));
    out.extend(once(TokenTree::from(Group::new(
        Delimiter::Brace,
        from_raw_bytes,
    ))));
    out
}

fn from_str(s: &str) -> Result<decimal::d128, &'static str> {
    use decimal::{d128, Status};
    use std::str::FromStr;

    d128::set_status(Status::empty());
    let res = d128::from_str(s);

    let status = d128::get_status();
    if status.contains(Status::CONVERSION_SYNTAX) {
        Err("not a valid d128 number")
    } else if status.contains(Status::OVERFLOW) {
        Err("too large for a d128 number")
    } else if status.contains(Status::UNDERFLOW) {
        Err("too small for a d128 number")
    } else if !status.is_empty() {
        Err("not a valid d128 number")
    } else {
        Ok(res.unwrap())
    }
}
