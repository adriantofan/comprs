use std::any::{Any, TypeId};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use crate::{Parser, ParseResult};

#[derive(Clone)]
struct CachedResult<Output>(Result<(usize, Output), usize>);

// used to give unique identity to each memoized parser
fn get_id() -> usize {
    static COUNTER: AtomicUsize = AtomicUsize::new(1);
    COUNTER.fetch_add(1, Ordering::Relaxed)
}

// first parameter is the input length, second is the parser hash, third is the type of the parser result
type MemoKey = (usize, usize, TypeId);

// TODO: it would be nice for it to be private
pub type ParseContext = Rc<RefCell<ParseCache>>;

pub struct ParseCache {
    memo_table : HashMap<MemoKey, Box<dyn Any>>,
}

pub fn new_parse_context() -> Rc<RefCell<ParseCache>> {
    Rc::new(RefCell::new(ParseCache::new()))
}

impl ParseCache {
    fn new() -> Self {
        ParseCache {
            memo_table: HashMap::new(),
        }
    }
}

pub struct Memoized<P> {
    parser: P,
    id: usize,
}

// CachedResult stores enough info about a ParserResult to be able to build a identical one
//  uses a unique id to identify the parser result in the memo table. This id is generated at parser
//  creation time and it is unique for each parser
pub fn memoize<P, Output>(parser: P) -> Memoized<P>
where
    P: Parser<Output>,
{
    Memoized {
        parser,
        id : get_id(),
    }
}

// Discussion: why is it reasonable to make copy a requirement for the Output type ?
//   - it is not possible to clone a Box<dyn Parser<Output>> because it is not Clone
//   - running the parser would be at least as expensive as cloning the result

impl<P, Output:Clone + 'static> Parser<Output> for Memoized<P>
    where
        P: Parser<Output>
{
    fn parse<'a>(&self, input: &'a str, ctx: ParseContext) -> ParseResult<'a, Output> {
        let key = (input.len(), self.id, TypeId::of::<CachedResult<Output>>());

        if let Some(result) = ctx.borrow().memo_table.get(&key) {
            let cached = result.downcast_ref::<CachedResult<Output>>().unwrap();
            match &cached.0 {
                Ok((rest, output)) => {
                    debug_assert_eq!(true, input.len() >= *rest);
                    let next_start = input.len() - rest;
                    return Ok((&input[next_start..], output.clone()));

                }
                Err(_rest) => {
                    debug_assert_eq!(*_rest, input.len());
                    return Err(input);
                }
            }
        };
        let result = self.parser.parse(input, ctx.clone());
        let memo:Box<CachedResult<Output>> = Box::new(match &result {
            // FIXME: put some numbers
            Ok((remaining, result)) => CachedResult(Ok((remaining.len(), result.clone()))),
            Err(remaining) => CachedResult(Err(remaining.len()))
        });
        ctx.borrow_mut().memo_table.insert(key, memo);
        result
    }
}

#[cfg(test)]
mod tests {
    use crate::{and, or, string};
    use super::*;


    #[test]
    fn test_memoize_with_parser_result_implementing_copy() {
        static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);
        // Still needs to derive clone but it builds a shallow clone (invokes copy)
        //  https://github.com/rust-lang/rust/pull/31414
        #[derive(Clone, Copy, PartialEq, Debug)]
        enum Output {
            Two,
        }

        fn p1(input: &str, _: ParseContext) -> ParseResult<Output> {
            CALL_COUNT.fetch_add(1, Ordering::Relaxed);
            Ok((input, Output::Two))
        }
        let parse = memoize(p1);
        let ctx = new_parse_context();
        assert_eq!(Ok(("", Output::Two)), parse.parse("", ctx.clone()));
        assert_eq!(Ok(("", Output::Two)), parse.parse("", ctx.clone()));
        assert_eq!(CALL_COUNT.load(Ordering::Relaxed), 1);
    }


    #[test]
    fn test_memoize_with_parser_result_recursive_enum() {
        static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);
        #[derive(Clone, PartialEq, Debug)]
        enum Output {
            One,
            Two(Box<Output>),
        }

        fn p1(input: &str, _: ParseContext) -> ParseResult<Output> {
            CALL_COUNT.fetch_add(1, Ordering::Relaxed);
            Ok((input, Output::Two(Box::new(Output::One))))
        }
        let parse = memoize(p1);
        let ctx = new_parse_context();
        assert_eq!(Ok(("", Output::Two(Box::new(Output::One)))), parse.parse("", ctx.clone()));
        assert_eq!(Ok(("", Output::Two(Box::new(Output::One)))), parse.parse("", ctx.clone()));
        assert_eq!(CALL_COUNT.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_memoize_position_is_remembered_correctly() {
        // Going to parse twice the same input with a sequence of two parsers, the second one
        //  being memoized.
        static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);

        fn second(input: &str, ctx: ParseContext) -> ParseResult<(())> {
            CALL_COUNT.fetch_add(1, Ordering::Relaxed);
            string("next").parse(input, ctx)
        }
        fn p1(input: &str, ctx: ParseContext) -> ParseResult<((),())> {
            and(string("first"), memoize(second)).parse(input, ctx)
        }
        let ctx = new_parse_context();
        assert_eq!(Ok(("rest", ((),()))), p1("firstnextrest", ctx.clone()));
        assert_eq!(Ok(("rest", ((),()))), p1("firstnextrest", ctx));
        assert_eq!(CALL_COUNT.load(Ordering::Relaxed), 1);
    }
}
