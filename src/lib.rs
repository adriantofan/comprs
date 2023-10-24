use crate::memoize::{memoize_with_id, ParseContext};
use std::rc::Rc;

pub mod memoize;

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

struct Terminal {
    t: &'static str,
}

pub fn terminal(t: &'static str) -> impl Parser<()> {
    Terminal { t: t }
}

impl Parser<()> for Terminal {
    fn parse<'a>(&self, input: &'a str, _: ParseContext) -> ParseResult<'a, ()> {
        match input.get(0..self.t.len()) {
            Some(next) if next == self.t => Ok((&input[self.t.len()..], ())),
            _ => Err(input),
        }
    }
}

struct Predicate<P> {
    predicate: P,
}

fn predicate<P>(p: P) -> Predicate<P>
where
    P: Fn(char) -> bool,
{
    Predicate { predicate: p }
}

impl<P> Parser<String> for Predicate<P>
where
    P: Fn(char) -> bool,
{
    fn parse<'a>(&self, input: &'a str, _: ParseContext) -> ParseResult<'a, String> {
        let mut prefix_length = 0;

        for (index, char) in input.chars().enumerate() {
            if !(self.predicate)(char) {
                break;
            }
            prefix_length = index + 1;
        }
        if prefix_length == 0 {
            return Err(input);
        }

        Ok((&input[prefix_length..], input[0..prefix_length].to_string()))
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
        self.parser1
            .parse(input, ctx.clone())
            .and_then(|(next_input, result1)| {
                self.parser2
                    .parse(next_input, ctx)
                    .map(|(last_input, result2)| (last_input, (result1, result2)))
            })
    }
}

struct Or<P1, P2> {
    parser1: P1,
    parser2: P2,
}

fn or_rec<P1, P2, Output: Clone + 'static>(
    id: usize,
    parser1: P1,
    parser2: P2,
) -> impl Parser<Output>
where
    P1: Parser<Output>,
    P2: Parser<Output>,
{
    memoize_with_id(Or { parser1, parser2 }, id)
}
// Note: or with memoize in itself does not work for recursive calls
//   because each recursive call will have a different id in the memo table
//   One solution is to use closures to create the recursive parser,
//     but the closures can't be recursive
//   Other solution would be to use a forward parser - which can't be written in rust
//   Lastly it might be possible to use fixed point combinator that would
//     allow a closure to call itself ... TBD...
#[allow(dead_code)]
fn or<P1, P2, Output: Clone + 'static>(parser1: P1, parser2: P2) -> impl Parser<Output>
where
    P1: Parser<Output>,
    P2: Parser<Output>,
{
    Or { parser1, parser2 }
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

struct Map<P, F, Output2> {
    parser: P,
    f: F,
    _output1: std::marker::PhantomData<Output2>,
}

fn map<P, F, Output2>(parser: P, f: F) -> Map<P, F, Output2> {
    Map {
        parser,
        f,
        _output1: std::marker::PhantomData,
    }
}

impl<P, F, Output1, Output2> Parser<Output2> for Map<P, F, Output1>
where
    P: Parser<Output1>,
    F: Fn(Output1) -> Output2,
{
    fn parse<'a>(&self, input: &'a str, ctx: ParseContext) -> ParseResult<'a, Output2> {
        self.parser
            .parse(input, ctx)
            .map(|(remainder, result)| (remainder, (self.f)(result)))
    }
}

impl<T, Output> Parser<Output> for Rc<T>
where
    T: Parser<Output>,
{
    fn parse<'a>(&self, input: &'a str, ctx: ParseContext) -> ParseResult<'a, Output> {
        self.as_ref().parse(input, ctx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memoize::new_parse_context;

    #[test]
    fn test_predicate() {
        let digit = predicate(|c| c.is_digit(10));
        assert_eq!(
            Ok(("", "123".to_string())),
            digit.parse("123", new_parse_context())
        );
        assert_eq!(
            Ok(("rest", "123".to_string())),
            digit.parse("123rest", new_parse_context())
        );
        assert_eq!(Err(""), digit.parse("", new_parse_context()));
    }

    #[test]
    fn literal_parse() {
        let parse_boom = terminal("boom!");
        assert_eq!(Ok(("", ())), parse_boom.parse("boom!", new_parse_context()));
        assert_eq!(
            Ok((" bang!", ())),
            parse_boom.parse("boom! bang!", new_parse_context())
        );
        assert_eq!(
            Err("booooom!"),
            parse_boom.parse("booooom!", new_parse_context())
        );
        // and
    }
    #[test]
    fn and_parse() {
        let parse_boombang = and(terminal("boom"), terminal("bang"));
        assert_eq!(
            Ok((" rest", ((), ()))),
            parse_boombang.parse("boombang rest", new_parse_context())
        );
        assert_eq!(
            Err("wrong"),
            parse_boombang.parse("wrong", new_parse_context())
        );
        assert_eq!(
            Err("wrong"),
            parse_boombang.parse("boomwrong", new_parse_context())
        );
    }

    #[test]
    fn left_recursion() {
        #[derive(Clone, PartialEq, Debug)]
        enum PlusExp {
            Plus(Box<PlusExp>, Box<PlusExp>),
            One,
        }
        static PLUS_EXP_ID: usize = 0;
        fn parse_plus_exp(input: &str, ctx: ParseContext) -> ParseResult<PlusExp> {
            or_rec(
                PLUS_EXP_ID,
                map(
                    and(
                        map(and(parse_plus_exp, terminal("+")), |(e, _)| e),
                        terminal("1"),
                    ),
                    |(e, _)| PlusExp::Plus(Box::new(e), Box::new(PlusExp::One)),
                ),
                map(terminal("1"), |_| PlusExp::One),
            )
            .parse(input, ctx)
        }

        assert_eq!(
            Ok(("", PlusExp::One)),
            parse_plus_exp("1", new_parse_context())
        );
        assert_eq!(
            Ok((
                "",
                PlusExp::Plus(
                    Box::new(PlusExp::Plus(
                        Box::new(PlusExp::One),
                        Box::new(PlusExp::One)
                    )),
                    Box::new(PlusExp::One),
                )
            )),
            parse_plus_exp("1+1+1", new_parse_context())
        );
    }

    #[test]
    fn simple_math() {
        // expression := expression "+" integer |
        //                              integer
        // integer    := [0-9]*
        #[derive(Clone, PartialEq, Debug)]
        enum Exp {
            Plus(Box<Exp>, Box<Exp>),
            // Minus(Box<Exp>, Box<Exp>),
            Number(i32),
        }
        // let number = many()

        static PLUS_EXP_ID: usize = 0;

        fn parse_number(input: &str, ctx: ParseContext) -> ParseResult<Exp> {
            // integer    := [0-9]*
            map(predicate(|c| c.is_digit(10)), |s: String| {
                // does not account for numbers starting with 0
                Exp::Number(s.parse::<i32>().unwrap())
            })
            .parse(input, ctx)
        }
        fn parse_exp(input: &str, ctx: ParseContext) -> ParseResult<Exp> {
            // expression := expression "+" integer |
            //                              integer
            or_rec(
                PLUS_EXP_ID,
                map(
                    and(
                        // expression "+" integer
                        map(and(parse_exp, terminal("+")), |(e, _)| e), // expression "+"
                        parse_number,
                    ),
                    |(e, number)| Exp::Plus(Box::new(e), Box::new(number)),
                ),
                parse_number,
            )
            .parse(input, ctx)
        }

        assert_eq!(
            Ok(("", Exp::Number(234))),
            parse_exp("234", new_parse_context())
        );
        assert_eq!(
            Ok((
                "",
                Exp::Plus(
                    Box::new(Exp::Plus(
                        Box::new(Exp::Number(1)),
                        Box::new(Exp::Number(2))
                    )),
                    Box::new(Exp::Number(3)),
                )
            )),
            parse_exp("1+2+3", new_parse_context())
        );
    }
}
