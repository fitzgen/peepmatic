/*!

This module implements parsing the DSL text format. It implements the
`wast::Parse` trait for all of our AST types.

The grammar for the DSL is given below:

```ebnf
<optimizations> ::= <optimization>*

<optimization> ::= '(' '=>' <lhs> <rhs> ')'

<left-hand-side> ::= <pattern>
                   | '(' 'when' <pattern> <precondition>* ')'

<pattern> ::= <value-literal>
            | <constant>
            | <operation<pattern>>
            | <variable>

<value-literal> ::= <integer>
                  | <boolean>

<boolean> ::= 'true' | 'false'

<operation<T>> ::= '(' <operator> <T>* ')'

<precondition> ::= '(' <constraint> <constraint-operands>* ')'

<constraint-operand> ::= <value-literal>
                       | <constant>
                       | <variable>

<rhs> ::= <value-literal>
        | <constant>
        | <variable>
        | <unquote>
        | <operation<rhs>>

<unquote> ::= '$' '(' <unquote-operator> <unquote-operand>* ')'

<unquote-operand> ::= <value-literal>
                    | <constant>
```

 */

use crate::ast::*;
use std::marker::PhantomData;
use wast::{
    parser::{Cursor, Parse, Parser, Peek, Result as ParseResult},
    Id, LParen,
};

mod tok {
    use wast::{custom_keyword, custom_reserved};

    custom_keyword!(ashr);
    custom_keyword!(bit_width = "bit-width");
    custom_keyword!(bor);
    custom_reserved!(dollar = "$");
    custom_keyword!(r#false = "false");
    custom_keyword!(iadd);
    custom_keyword!(iadd_imm);
    custom_keyword!(iconst);
    custom_keyword!(imul);
    custom_keyword!(ishl);
    custom_keyword!(isub);
    custom_keyword!(is_power_of_two = "is-power-of-two");
    custom_keyword!(log2);
    custom_reserved!(replace = "=>");
    custom_keyword!(sshr);
    custom_keyword!(r#true = "true");
    custom_keyword!(when);
}

impl<'a> Parse<'a> for Optimizations<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        let mut optimizations = vec![];
        while !p.is_empty() {
            optimizations.push(p.parse()?);
        }
        Ok(Optimizations {
            span,
            optimizations,
        })
    }
}

impl<'a> Parse<'a> for Optimization<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        p.parens(|p| {
            p.parse::<tok::replace>()?;
            let lhs = p.parse()?;
            let rhs = p.parse()?;
            Ok(Optimization { span, lhs, rhs })
        })
    }
}

impl<'a> Parse<'a> for Lhs<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        let mut preconditions = vec![];
        if p.peek::<wast::LParen>() && p.peek2::<tok::when>() {
            p.parens(|p| {
                p.parse::<tok::when>()?;
                let pattern = p.parse()?;
                while p.peek::<LParen>() {
                    preconditions.push(p.parse()?);
                }
                Ok(Lhs {
                    span,
                    pattern,
                    preconditions,
                })
            })
        } else {
            let span = p.cur_span();
            let pattern = p.parse()?;
            Ok(Lhs {
                span,
                pattern,
                preconditions,
            })
        }
    }
}

impl<'a> Parse<'a> for Pattern<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        if p.peek::<ValueLiteral>() {
            return Ok(Pattern::ValueLiteral(p.parse()?));
        }
        if p.peek::<Constant>() {
            return Ok(Pattern::Constant(p.parse()?));
        }
        if p.peek::<Operation<Self>>() {
            return Ok(Pattern::Operation(p.parse()?));
        }
        if p.peek::<Variable>() {
            return Ok(Pattern::Variable(p.parse()?));
        }
        Err(p.error("expected a left-hand side pattern"))
    }
}

impl<'a> Peek for Pattern<'a> {
    fn peek(c: Cursor) -> bool {
        ValueLiteral::peek(c)
            || Constant::peek(c)
            || Variable::peek(c)
            || Operation::<Self>::peek(c)
    }

    fn display() -> &'static str {
        "left-hand side pattern"
    }
}

impl<'a> Parse<'a> for ValueLiteral<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        if let Ok(b) = p.parse::<Boolean>() {
            return Ok(ValueLiteral::Boolean(b));
        }
        if let Ok(i) = p.parse::<Integer>() {
            return Ok(ValueLiteral::Integer(i));
        }
        Err(p.error("expected an integer or boolean literal"))
    }
}

impl<'a> Peek for ValueLiteral<'a> {
    fn peek(c: Cursor) -> bool {
        c.integer().is_some() || Boolean::peek(c)
    }

    fn display() -> &'static str {
        "value literal"
    }
}

impl<'a> Parse<'a> for Integer<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        p.step(|c| {
            if let Some((i, rest)) = c.integer() {
                let (s, base) = i.val();
                let val = i128::from_str_radix(s, base)
                    .or_else(|_| u128::from_str_radix(s, base).map(|i| i as i128));
                return match val {
                    Ok(value) => Ok((
                        Integer {
                            span,
                            value,
                            marker: PhantomData,
                        },
                        rest,
                    )),
                    Err(_) => Err(c.error("invalid integer: out of range")),
                };
            }
            Err(c.error("expected an integer"))
        })
    }
}

impl<'a> Parse<'a> for Boolean<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        if p.parse::<tok::r#true>().is_ok() {
            return Ok(Boolean {
                span,
                value: true,
                marker: PhantomData,
            });
        }
        if p.parse::<tok::r#false>().is_ok() {
            return Ok(Boolean {
                span,
                value: false,
                marker: PhantomData,
            });
        }
        Err(p.error("expected `true` or `false`"))
    }
}

impl<'a> Peek for Boolean<'a> {
    fn peek(c: Cursor) -> bool {
        <tok::r#true as Peek>::peek(c) || <tok::r#false as Peek>::peek(c)
    }

    fn display() -> &'static str {
        "boolean `true` or `false`"
    }
}

impl<'a> Parse<'a> for Constant<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        let id = Id::parse(p)?;
        if id
            .name()
            .chars()
            .all(|c| !c.is_alphabetic() || c.is_uppercase())
        {
            Ok(Constant { span, id })
        } else {
            let upper = id
                .name()
                .chars()
                .flat_map(|c| c.to_uppercase())
                .collect::<String>();
            Err(p.error(format!(
                "symbolic constants must start with an upper-case letter like ${}",
                upper
            )))
        }
    }
}

impl<'a> Peek for Constant<'a> {
    fn peek(c: Cursor) -> bool {
        if let Some((id, _rest)) = c.id() {
            id.chars().all(|c| !c.is_alphabetic() || c.is_uppercase())
        } else {
            false
        }
    }

    fn display() -> &'static str {
        "symbolic constant"
    }
}

impl<'a> Parse<'a> for Variable<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        let id = Id::parse(p)?;
        if id
            .name()
            .chars()
            .all(|c| !c.is_alphabetic() || c.is_lowercase())
        {
            Ok(Variable { span, id })
        } else {
            let lower = id
                .name()
                .chars()
                .flat_map(|c| c.to_lowercase())
                .collect::<String>();
            Err(p.error(format!(
                "variables must start with an lower-case letter like ${}",
                lower
            )))
        }
    }
}

impl<'a> Peek for Variable<'a> {
    fn peek(c: Cursor) -> bool {
        if let Some((id, _rest)) = c.id() {
            id.chars().all(|c| !c.is_alphabetic() || c.is_lowercase())
        } else {
            false
        }
    }

    fn display() -> &'static str {
        "variable"
    }
}

impl<'a, T> Parse<'a> for Operation<'a, T>
where
    T: 'a + Ast<'a> + Peek + Parse<'a>,
    DynAstRef<'a>: From<&'a T>,
{
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        p.parens(|p| {
            let operator = p.parse()?;
            let mut operands = vec![];
            while p.peek::<T>() {
                operands.push(p.parse()?);
            }
            Ok(Operation {
                span,
                operator,
                operands,
                marker: PhantomData,
            })
        })
    }
}

impl<'a, T> Peek for Operation<'a, T>
where
    T: 'a + Ast<'a>,
    DynAstRef<'a>: From<&'a T>,
{
    fn peek(c: Cursor) -> bool {
        wast::LParen::peek(c)
    }

    fn display() -> &'static str {
        "operation"
    }
}

impl<'a> Parse<'a> for Operator {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        if p.peek::<tok::ashr>() {
            p.parse::<tok::ashr>()?;
            return Ok(Operator::Ashr);
        }
        if p.peek::<tok::bor>() {
            p.parse::<tok::bor>()?;
            return Ok(Operator::Bor);
        }
        if p.peek::<tok::iadd>() {
            p.parse::<tok::iadd>()?;
            return Ok(Operator::Iadd);
        }
        if p.peek::<tok::iadd_imm>() {
            p.parse::<tok::iadd_imm>()?;
            return Ok(Operator::IaddImm);
        }
        if p.peek::<tok::iconst>() {
            p.parse::<tok::iconst>()?;
            return Ok(Operator::Iconst);
        }
        if p.peek::<tok::imul>() {
            p.parse::<tok::imul>()?;
            return Ok(Operator::Imul);
        }
        if p.peek::<tok::ishl>() {
            p.parse::<tok::ishl>()?;
            return Ok(Operator::Ishl);
        }
        if p.peek::<tok::sshr>() {
            p.parse::<tok::sshr>()?;
            return Ok(Operator::Sshr);
        }
        Err(p.error("expected operator"))
    }
}

impl<'a> Parse<'a> for Precondition<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        p.parens(|p| {
            let constraint = p.parse()?;
            let mut operands = vec![];
            while p.peek::<ConstraintOperand>() {
                operands.push(p.parse()?);
            }
            Ok(Precondition {
                span,
                constraint,
                operands,
            })
        })
    }
}

impl<'a> Parse<'a> for Constraint {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        if p.peek::<tok::is_power_of_two>() {
            p.parse::<tok::is_power_of_two>()?;
            return Ok(Constraint::IsPowerOfTwo);
        }
        if p.peek::<tok::bit_width>() {
            p.parse::<tok::bit_width>()?;
            return Ok(Constraint::BitWidth);
        }
        Err(p.error("expected a precondition constraint"))
    }
}

impl<'a> Parse<'a> for ConstraintOperand<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        if p.peek::<ValueLiteral>() {
            return Ok(ConstraintOperand::ValueLiteral(p.parse()?));
        }
        if p.peek::<Constant>() {
            return Ok(ConstraintOperand::Constant(p.parse()?));
        }
        if p.peek::<Variable>() {
            return Ok(ConstraintOperand::Variable(p.parse()?));
        }
        Err(p.error("expected an operand for precondition constraint"))
    }
}

impl<'a> Peek for ConstraintOperand<'a> {
    fn peek(c: Cursor) -> bool {
        ValueLiteral::peek(c) || Constant::peek(c) || Variable::peek(c)
    }

    fn display() -> &'static str {
        "operand for a precondition constraint"
    }
}

impl<'a> Parse<'a> for Rhs<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        if p.peek::<ValueLiteral>() {
            return Ok(Rhs::ValueLiteral(p.parse()?));
        }
        if p.peek::<Constant>() {
            return Ok(Rhs::Constant(p.parse()?));
        }
        if p.peek::<Variable>() {
            return Ok(Rhs::Variable(p.parse()?));
        }
        if p.peek::<Unquote>() {
            return Ok(Rhs::Unquote(p.parse()?));
        }
        if p.peek::<Operation<Self>>() {
            return Ok(Rhs::Operation(p.parse()?));
        }
        Err(p.error("expected a right-hand side replacement"))
    }
}

impl<'a> Peek for Rhs<'a> {
    fn peek(c: Cursor) -> bool {
        ValueLiteral::peek(c)
            || Constant::peek(c)
            || Variable::peek(c)
            || Unquote::peek(c)
            || Operation::<Self>::peek(c)
    }

    fn display() -> &'static str {
        "right-hand side replacement"
    }
}

impl<'a> Parse<'a> for Unquote<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        let span = p.cur_span();
        p.parse::<tok::dollar>()?;
        p.parens(|p| {
            let operator = p.parse()?;
            let mut operands = vec![];
            while p.peek::<UnquoteOperand>() {
                operands.push(p.parse()?);
            }
            Ok(Unquote {
                span,
                operator,
                operands,
            })
        })
    }
}

impl<'a> Peek for Unquote<'a> {
    fn peek(c: Cursor) -> bool {
        tok::dollar::peek(c)
    }

    fn display() -> &'static str {
        "unquote expression"
    }
}

impl<'a> Parse<'a> for UnquoteOperator {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        if p.peek::<tok::log2>() {
            p.parse::<tok::log2>()?;
            return Ok(UnquoteOperator::Log2);
        }
        Err(p.error("expected an operator for an unquote expression"))
    }
}

impl<'a> Parse<'a> for UnquoteOperand<'a> {
    fn parse(p: Parser<'a>) -> ParseResult<Self> {
        if p.peek::<ValueLiteral>() {
            return Ok(UnquoteOperand::ValueLiteral(p.parse()?));
        }
        if p.peek::<Constant>() {
            return Ok(UnquoteOperand::Constant(p.parse()?));
        }
        Err(p.error("expected an operand for an unquote expression"))
    }
}

impl<'a> Peek for UnquoteOperand<'a> {
    fn peek(c: Cursor) -> bool {
        ValueLiteral::peek(c) || Constant::peek(c)
    }

    fn display() -> &'static str {
        "operand for unquote expression"
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! test_parse {
        (
            $(
                $name:ident < $ast:ty > {
                    $( ok { $( $ok:expr , )* } )*
                    $( err { $( $err:expr , )* } )*
                }
            )*
        ) => {
            $(
                #[test]
                #[allow(non_snake_case)]
                fn $name() {
                    $(
                        $({
                            let input = $ok;
                            let buf = wast::parser::ParseBuffer::new(input).unwrap_or_else(|e| {
                                panic!("should lex OK, got error:\n\n{}\n\nInput:\n\n{}", e, input)
                            });
                            if let Err(e) = wast::parser::parse::<$ast>(&buf) {
                                panic!(
                                    "expected to parse OK, got error:\n\n{}\n\nInput:\n\n{}",
                                    e, input
                                );
                            }
                        })*
                    )*

                    $(
                        $({
                            let input = $err;
                            let buf = wast::parser::ParseBuffer::new(input).unwrap_or_else(|e| {
                                panic!("should lex OK, got error:\n\n{}\n\nInput:\n\n{}", e, input)
                            });
                            if let Ok(ast) = wast::parser::parse::<$ast>(&buf) {
                                panic!(
                                    "expected a parse error, got:\n\n{:?}\n\nInput:\n\n{}",
                                    ast, input
                                );
                            }
                        })*
                    )*
                }
            )*
        }
    }

    test_parse! {
        parse_boolean<Boolean> {
            ok {
                "true",
                "false",
            }
            err {
                "",
                "t",
                "tr",
                "tru",
                "truezzz",
                "f",
                "fa",
                "fal",
                "fals",
                "falsezzz",
            }
        }
        parse_constant<Constant> {
            ok {
                "$C",
                "$C1",
                "$C2",
                "$X",
                "$Y",
                "$SOME-CONSTANT",
                "$SOME_CONSTANT",
            }
            err {
                "",
                "zzz",
                "$",
                "$variable",
                "$Some-Constant",
                "$Some_Constant",
                "$Some_constant",
            }
        }
        parse_constraint<Constraint> {
            ok {
                "is-power-of-two",
                "bit-width",
            }
            err {
                "",
                "iadd",
                "imul",
            }
        }
        parse_constraint_operand<ConstraintOperand> {
            ok {
                "1234",
                "true",
                "$CONSTANT",
                "$variable",
            }
            err {
                "",
                "is-power-of-two",
                "(is-power-of-two $C)",
                "(iadd 1 2)",
            }
        }
        parse_integer<Integer> {
            ok {
                "0",
                "1",
                "12",
                "123",
                "1234",
                "12345",
                "123456",
                "1234567",
                "12345678",
                "123456789",
                "1234567890",
                "0x0",
                "0x1",
                "0x12",
                "0x123",
                "0x1234",
                "0x12345",
                "0x123456",
                "0x1234567",
                "0x12345678",
                "0x123456789",
                "0x123456789a",
                "0x123456789ab",
                "0x123456789abc",
                "0x123456789abcd",
                "0x123456789abcde",
                "0x123456789abcdef",
                "0xffff_ffff_ffff_ffff",
            }
            err {
                "",
                "abcdef",
                "01234567890abcdef",
                "0xgggg",
                "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            }
        }
        parse_lhs<Lhs> {
            ok {
                "(when (imul $C1 $C2) (is-power-of-two $C1) (is-power-of-two $C2))",
                "(when (imul $x $C) (is-power-of-two $C))",
                "(imul $x $y)",
                "(imul $x)",
                "(imul)",
                "$C",
                "$x",
            }
            err {
                "",
                "()",
                "abc",
            }
        }
        parse_operation_pattern<Operation<Pattern>> {
            ok {
                "(iadd)",
                "(iadd 1)",
                "(iadd 1 2)",
                "(iadd $x $C)",
            }
            err {
                "",
                "()",
                "$var",
                "$CONST",
                "(ishl $x $(log2 $C))",
            }
        }
        parse_operation_rhs<Operation<Rhs>> {
            ok {
                "(iadd)",
                "(iadd 1)",
                "(iadd 1 2)",
                "(ishl $x $(log2 $C))",
            }
            err {
                "",
                "()",
                "$var",
                "$CONST",
            }
        }
        parse_operator<Operator> {
            ok {
                "ashr",
                "bor",
                "iadd",
                "iadd_imm",
                "iconst",
                "imul",
                "ishl",
                "sshr",
            }
            err {
                "",
                "iadd.i32",
            }
        }
        parse_optimization<Optimization> {
            ok {
                "(=> (when (iadd $x $C) (is-power-of-two $C) (is-power-of-two $C)) (iadd $C $x))",
                "(=> (when (iadd $x $C)) (iadd $C $x))",
                "(=> (iadd $x $C) (iadd $C $x))",
            }
            err {
                "",
                "()",
                "(=>)",
                "(=> () ())",
            }
        }
        parse_optimizations<Optimizations> {
            ok {
                "",
                r#"
                ;; Canonicalize `a + (b + c)` into `(a + b) + c`.
                (=> (iadd $a (iadd $b $c))
                    (iadd (iadd $a $b) $c))

                ;; Combine a `const` and an `iadd` into a `iadd_imm`.
                (=> (iadd (iconst $C) $x)
                    (iadd_imm $C $x))

                ;; When `C` is a power of two, replace `x * C` with `x << log2(C)`.
                (=> (when (imul $x $C)
                          (is-power-of-two $C))
                    (ishl $x $(log2 $C)))
                "#,
            }
        }
        parse_pattern<Pattern> {
            ok {
                "1234",
                "$C",
                "$x",
                "(iadd $x $y)",
            }
            err {
                "",
                "()",
                "abc",
            }
        }
        parse_precondition<Precondition> {
            ok {
                "(is-power-of-two)",
                "(is-power-of-two $C)",
                "(is-power-of-two $C1 $C2)",
            }
            err {
                "",
                "1234",
                "()",
                "$var",
                "$CONST",
            }
        }
        parse_rhs<Rhs> {
            ok {
                "5",
                "$C",
                "$x",
                "$(log2 $C)",
                "(iadd $x 1)",
            }
            err {
                "",
                "()",
            }
        }
        parse_unquote<Unquote> {
            ok {
                "$(log2)",
                "$(log2 $C)",
                "$(log2 $C1 1)",
            }
            err {
                "",
                "(log2 $C)",
                "$()",
            }
        }
        parse_unquote_operand<UnquoteOperand> {
            ok {
                "5",
                "$C",
            }
            err {
                "",
                "$x",
                "(iadd 1 2)",
            }
        }
        parse_value_literal<ValueLiteral> {
            ok {
                "12345",
                "true",
            }
            err {
                "",
                "'c'",
                "\"hello\"",
                "12.34",
            }
        }
        parse_variable<Variable> {
            ok {
                "$v",
                "$v1",
                "$v2",
                "$x",
                "$y",
                "$some-var",
                "$another_var",
            }
            err {
                "zzz",
                "$",
                "$CONSTANT",
                "$fooBar",
            }
        }
    }
}
