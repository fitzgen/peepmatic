//! Operator definitions.

use peepmatic_macro::PeepmaticOperator;
use serde::{Deserialize, Serialize};

/// An operator.
///
/// These are a subset of Cranelift IR's operators.
#[derive(PeepmaticOperator, Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[repr(u32)]
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

    /// `sdiv`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Sdiv,

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
    custom_keyword!(sdiv);
    custom_keyword!(sshr);
}

impl<'a> wast::parser::Parse<'a> for Operator {
    fn parse(p: wast::parser::Parser<'a>) -> wast::parser::Result<Self> {
        macro_rules! parse {
            ( $( $tok:ident => $variant:ident , )* ) => {
                $(
                    if p.peek::<tok::$tok>() {
                        p.parse::<tok::$tok>()?;
                        return Ok(Operator::$variant);
                    }
                )*
            }
        }

        parse!(
            ashr => Ashr,
            bor => Bor,
            iadd => Iadd,
            iadd_imm => IaddImm,
            iconst => Iconst,
            imul => Imul,
            imul_imm => ImulImm,
            ishl => Ishl,
            sdiv => Sdiv,
            sshr => Sshr,
        );

        Err(p.error("expected operator"))
    }
}
