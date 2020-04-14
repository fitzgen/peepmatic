//! Operator definitions.

use peepmatic_macro::PeepmaticOperator;
use serde::{Deserialize, Serialize};

/// An operator.
///
/// These are a subset of Cranelift IR's operators.
#[derive(PeepmaticOperator, Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[repr(u32)]
pub enum Operator {
    /// `adjust_sp_down`
    #[peepmatic(params(iNN), result(void))]
    AdjustSpDown = 1,

    /// `adjust_sp_down_imm`
    #[peepmatic(immediates(iNN), result(void))]
    AdjustSpDownImm,

    /// `band`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Band,

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

    /// `icmp`
    #[peepmatic(params(iNN, iNN), result(b1))]
    Icmp,

    /// `icmp_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(b1))]
    IcmpImm,

    /// `iconst`
    #[peepmatic(immediates(iNN), result(iNN))]
    Iconst,

    /// `ifcmp`
    #[peepmatic(params(iNN, iNN), result(cpu_flags))]
    Ifcmp,

    /// `ifcmp_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(cpu_flags))]
    IfcmpImm,

    /// `imul`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Imul,

    /// `imul_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    ImulImm,

    /// `irsub_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    IrsubImm,

    /// `ishl`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Ishl,

    /// `ishl_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    IshlImm,

    /// `isub`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Isub,

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

/// Compile-time unquote operators.
///
/// These are used in the right-hand side to perform compile-time evaluation of
/// constants matched on the left-hand side.
#[derive(PeepmaticOperator, Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[repr(u32)]
pub enum UnquoteOperator {
    /// Take the base-2 log of a power of two integer.
    #[peepmatic(params(iNN), result(iNN))]
    Log2,

    /// Wrapping negation of an integer.
    #[peepmatic(params(iNN), result(iNN))]
    Neg,
}

/// A trait to represent a typing context.
///
/// This is used by the macro-generated operator methods that create the type
/// variables for their immediates, parameters, and results. This trait is
/// implemented by the concrete typing context in `peepmatic/src/verify.rs`.
#[cfg(feature = "construct")]
pub trait TypingContext<'a> {
    /// A type variable.
    type TypeVariable;

    /// Create an integer type with a polymorphic bit width.
    #[allow(non_snake_case)]
    fn iNN(&mut self, span: wast::Span) -> Self::TypeVariable;

    /// Create the CPU flags type variable.
    fn cpu_flags(&mut self, span: wast::Span) -> Self::TypeVariable;

    /// Create a boolean type of size one bit.
    fn b1(&mut self, span: wast::Span) -> Self::TypeVariable;

    /// Create the void type, used as the result of operators that branch away,
    /// or do not return anything.
    fn void(&mut self, span: wast::Span) -> Self::TypeVariable;
}
