//! Operator definitions.

use peepmatic_macro::PeepmaticOperator;
use serde::{Deserialize, Serialize};

/// An operator.
///
/// These are a subset of Cranelift IR's operators.
#[derive(PeepmaticOperator, Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[repr(u32)]
pub enum Operator {
    /// `band`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Band = 1,

    /// `band_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    BandImm,

    /// `bor`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Bor,

    /// `bor_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    BorImm,

    /// `bxor`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Bxor,

    /// `bxor_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    BxorImm,

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

    /// `ishl_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    IshlImm,

    /// `isub`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Isub,

    /// `isub_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    IsubImm,

    /// `rotl`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Rotl,

    /// `rotl_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    RotlImm,

    /// `rotr`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Rotr,

    /// `rotr_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    RotrImm,

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

    /// `sshr_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    SshrImm,

    /// `udiv`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Udiv,

    /// `udiv_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    UdivImm,

    /// `urem`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Urem,

    /// `urem_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    UremImm,

    /// `ushr`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Ushr,

    /// `ushr_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    UshrImm,
}

/// TODO FITZGEN
pub trait TypingContext<'a> {
    /// TODO FITZGEN
    type TypeVariable;

    /// TODO FITZGEN
    #[allow(non_snake_case)]
    fn iNN(&mut self, span: wast::Span) -> Self::TypeVariable;
}
