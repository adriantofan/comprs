use crate::{ParseResult, Parser};
use std::any::{Any, TypeId};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone)]
struct CachedResult<Output>(Result<(usize, Output), usize>);

// used to give unique identity to each memoized parser
fn get_id() -> usize {
    static COUNTER: AtomicUsize = AtomicUsize::new(1);
    COUNTER.fetch_add(1, Ordering::Relaxed)
}

// first parameter is the input length, second is the parser i, third is the type of the parser result
type MemoKey = (usize, usize, TypeId);

pub type ParseContext = Rc<RefCell<ParseCache>>;

pub struct ParseCache {
    memo_table: HashMap<MemoKey, Box<dyn Any>>,
    recursion_table: HashMap<MemoKey, usize>,
}

pub fn new_parse_context() -> Rc<RefCell<ParseCache>> {
    Rc::new(RefCell::new(ParseCache::new()))
}

impl ParseCache {
    fn new() -> Self {
        ParseCache {
            memo_table: HashMap::new(),
            recursion_table: HashMap::new(),
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
        id: get_id(),
    }
}

pub fn memoize_with_id<P, Output>(parser: P, id: usize) -> Memoized<P>
where
    P: Parser<Output>,
{
    Memoized { parser, id }
}

impl<P, Output: Clone + 'static> Parser<Output> for Memoized<P>
where
    P: Parser<Output>,
{
    fn parse<'a>(&self, input: &'a str, ctx: ParseContext) -> ParseResult<'a, Output> {
        let key = (input.len(), self.id, TypeId::of::<CachedResult<Output>>());

        if let Some(result) = ctx.borrow().memo_table.get(&key) {
            // Extract and return a newly built  result from the cached value
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

        {
            let mut ctx_mut = ctx.borrow_mut();
            if let Some(depth) = ctx_mut.recursion_table.get_mut(&key) {
                let max_depth = input.len() + 1;
                *depth += 1;
                if *depth > max_depth {
                    // Fixme: it would be nice to have a message here
                    return Err(input);
                }
            } else {
                ctx_mut.recursion_table.insert(key, 1);
            }
        }

        let p = &self.parser;
        let ctx_clone = ctx.clone();
        let result = p.parse(input, ctx_clone);
        let memo: Box<CachedResult<Output>> = Box::new(match &result {
            // FIXME: put some numbers
            Ok((remaining, result)) => CachedResult(Ok((remaining.len(), result.clone()))),
            Err(remaining) => CachedResult(Err(remaining.len())),
        });
        ctx.borrow_mut().memo_table.insert(key, memo);

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{and, terminal};

    #[test]
    fn test_memoize_with_parser_result_implementing_copy() {
        static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);
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
        assert_eq!(
            Ok(("", Output::Two(Box::new(Output::One)))),
            parse.parse("", ctx.clone())
        );
        assert_eq!(
            Ok(("", Output::Two(Box::new(Output::One)))),
            parse.parse("", ctx.clone())
        );
        assert_eq!(CALL_COUNT.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_memoize_position_is_remembered_correctly() {
        // Going to parse twice the same input with a sequence of two parsers, the second one
        //  being memoized. This fails because the identity of the second parser is not taken into
        static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);

        fn second(input: &str, ctx: ParseContext) -> ParseResult<()> {
            CALL_COUNT.fetch_add(1, Ordering::Relaxed);
            terminal("next_").parse(input, ctx)
        }
        fn p1(input: &str, ctx: ParseContext) -> ParseResult<((), ())> {
            and(terminal("first_"), memoize_with_id(second, 1)).parse(input, ctx)
            // shows how, memoize is called at each run of the parser - making a fresh copy of the
            //  parser which in the memoize case gets the same id
        }

        let ctx = new_parse_context();
        assert_eq!(Ok(("rest", ((), ()))), p1("first_next_rest", ctx.clone()));
        assert_eq!(Ok(("rest", ((), ()))), p1("first_next_rest", ctx));
        assert_eq!(CALL_COUNT.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_memoize_auto_id_position_is_remembered_correctly() {
        static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);

        fn second(input: &str, ctx: ParseContext) -> ParseResult<()> {
            CALL_COUNT.fetch_add(1, Ordering::Relaxed);
            terminal("next_").parse(input, ctx)
        }

        let ctx = new_parse_context();
        let p1 = and(terminal("first_"), memoize(second));
        // Note how p1 cannot be recursive because it is not a function
        assert_eq!(
            Ok(("rest", ((), ()))),
            p1.parse("first_next_rest", ctx.clone())
        );
        assert_eq!(Ok(("rest", ((), ()))), p1.parse("first_next_rest", ctx));
        assert_eq!(CALL_COUNT.load(Ordering::Relaxed), 1);
    }
}
