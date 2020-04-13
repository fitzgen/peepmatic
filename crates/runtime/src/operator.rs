//! Operator definitions.

use peepmatic_macro::PeepmaticOperator;
use serde::{Deserialize, Serialize};

/// An operator.
///
/// These are a subset of Cranelift IR's operators.
#[derive(PeepmaticOperator, Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[repr(u8)]
pub enum Operator {
    /// `ashr`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Ashr = 1,

    /// `bor`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Bor,

    /// `iadd`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Iadd,

    /// `iadd_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    IaddImm,

    /// `iconst`
    #[peepmatic(immediates(iNN), result(iNN))]
    Iconst,

    /// `imul`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Imul,

    /// `imul_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    ImulImm,

    /// `ishl`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Ishl,

    /// `sshr`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Sshr,
}

/// TODO FITZGEN
pub trait TypingContext<'a> {
    /// TODO FITZGEN
    type TypeVariable;

    /// TODO FITZGEN
    #[allow(non_snake_case)]
    fn iNN(&mut self, span: wast::Span) -> Self::TypeVariable;
}

mod tok {
    use wast::custom_keyword;
    custom_keyword!(ashr);
    custom_keyword!(bor);
    custom_keyword!(iadd);
    custom_keyword!(iadd_imm);
    custom_keyword!(iconst);
    custom_keyword!(imul);
    custom_keyword!(imul_imm);
    custom_keyword!(ishl);
    custom_keyword!(isub);
    custom_keyword!(sshr);
}

impl<'a> wast::parser::Parse<'a> for Operator {
    fn parse(p: wast::parser::Parser<'a>) -> wast::parser::Result<Self> {
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
        if p.peek::<tok::imul_imm>() {
            p.parse::<tok::imul_imm>()?;
            return Ok(Operator::ImulImm);
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
