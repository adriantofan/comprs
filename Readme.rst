A WIP for a Rust implementation of `parser combinators <https://en.wikipedia.org/wiki/Parser_combinator>`_. 
With this library, one can build up a complex parser from primitive parsers such as "get
one token" (the ``One`` parser), or compose parsers together such as "if this
parser fails, try that parser" (the ``Or`` combinator), etc. The mental model is
a binary tree of execution nodes through which a sequence of input tokens flows.

The main goal of this library is to supports memoization and curtailment
as described in [Frost2007]_. This allows a memoized parser to achieve
asymptotically best performance, and support ambiguous grammars.

The seccondary goal (WIP) is to experiment with declaratively building parsers.


.. code-block:: rust

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


References
==========

.. [Frost2007] Frost R.A., Hafiz R., Callaghan P. (2007) "Parser Combinators for
   Ambiguous Left-Recursive Grammars". In: Hudak P., Warren D.S. (eds)
   "Practical Aspects of Declarative Languages". PADL 2008. Lecture Notes in
   Computer Science, vol 4902. Springer, Berlin, Heidelberg