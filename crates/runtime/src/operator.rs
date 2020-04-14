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

    /// `sdiv_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    SdivImm,

    /// `srem`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Srem,

    /// `srem_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    SremImm,

    /// `sshr`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Sshr,

    /// `udiv`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Udiv,

    /// `udiv_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    UdivImm,
}

/// TODO FITZGEN
pub trait TypingContext<'a> {
    /// TODO FITZGEN
    type TypeVariable;

    /// TODO FITZGEN
    #[allow(non_snake_case)]
    fn iNN(&mut self, span: wast::Span) -> Self::TypeVariable;
}
