use crate::memoize::{memoize, ParseContext};

mod memoize;

type ParseResult<'a, O> = Result<(&'a str, O), &'a str>;

pub trait Parser<Output> {
    fn parse<'a>(&self, input: &'a str, ctx: ParseContext) -> ParseResult<'a, Output>;
}


impl<F, Output> Parser<Output> for F
    where
        F: Fn(&str, ParseContext) -> ParseResult<Output>,
{
    fn parse<'a>(&self, input: &'a str, ctx: ParseContext) -> ParseResult<'a, Output> {
        self(input, ctx)
    }
}

struct Str {
    expected: &'static str
}

fn string(expected: &'static str) -> impl Parser<()> {
    Str { expected }
}

impl Parser<()> for Str
{
    fn parse<'a>(&self, input: &'a str, _: ParseContext) -> ParseResult<'a, ()> {
        match input.get(0..self.expected.len()) {
            Some(next) if next == self.expected => Ok((&input[self.expected.len()..], ())),
            _ => Err(input),
        }
    }
}

struct And<P1, P2> {
    parser1: P1,
    parser2: P2,
}

fn and<P1, P2, Output1, Output2>(parser1: P1, parser2: P2) -> impl Parser<(Output1, Output2)>
    where
        P1: Parser<Output1>,
        P2: Parser<Output2>,
{
    And { parser1, parser2 }
}
impl<P1, P2, Output1, Output2> Parser<(Output1, Output2)> for And<P1, P2>
    where
        P1: Parser<Output1>,
        P2: Parser<Output2>,
{
    fn parse<'a>(&self, input: &'a str, ctx: ParseContext) -> ParseResult<'a, (Output1, Output2)> {
        self.parser1.parse(input,ctx.clone()).and_then(|(next_input, result1)| {
            self.parser2
                .parse(next_input,ctx)
                .map(|(last_input, result2)| (last_input, (result1, result2)))
        })
    }
}

struct Or<P1, P2> {
    parser1: P1,
    parser2: P2,
}

fn or<P1, P2, Output:Clone + 'static>(parser1: P1, parser2: P2) -> impl Parser<Output>
    where
        P1: Parser<Output>,
        P2: Parser<Output>,
{
    memoize(Or { parser1, parser2 })
}

impl<P1, P2, Output> Parser<Output> for Or<P1, P2>
    where
        P1: Parser<Output>,
        P2: Parser<Output>,
{
    fn parse<'a>(&self, input: &'a str, ctx: ParseContext) -> ParseResult<'a, Output> {
        match self.parser1.parse(input, ctx.clone()) {
            Ok((rest, result)) => Ok((rest, result)),
            Err(_) => self.parser2.parse(input, ctx),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::memoize::new_parse_context;
    use super::*;

    #[test]
    fn literal_parse() {
        let parse_boom = string("boom!");
        assert_eq!(Ok(("", ())), parse_boom.parse("boom!", new_parse_context()));
        assert_eq!(Ok((" bang!", ())), parse_boom.parse("boom! bang!", new_parse_context()));
        assert_eq!(Err("booooom!"), parse_boom.parse("booooom!", new_parse_context()));
        // and
    }
    #[test]
    fn and_parse() {
        let parse_boombang = and(string("boom"), string("bang"));
        assert_eq!(
            Ok((" rest", ((), ()))),
            parse_boombang.parse("boombang rest", new_parse_context())
        );
        assert_eq!(Err("wrong"), parse_boombang.parse("wrong", new_parse_context()));
        assert_eq!(Err("wrong"), parse_boombang.parse("boomwrong", new_parse_context()));
    }
}
