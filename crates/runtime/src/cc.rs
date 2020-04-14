//! Condition codes.

use serde::{Deserialize, Serialize};
use std::fmt;

/// A condition code.
///
/// This is a special kind of immediate for `icmp` and `ifcmp` instructions that
/// dictate which parts of the comparison result we care about.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u32)]
pub enum ConditionCode {
    /// Equal.
    Eq = 1,

    /// Not equal.
    Ne,

    /// Signed less than.
    Slt,

    /// Unsigned less than.
    Ult,

    /// Signed greater than or equal.
    Sge,

    /// Unsigned greater than or equal.
    Uge,

    /// Signed greater than.
    Sgt,

    /// Unsigned greater than.
    Ugt,

    /// Signed less than or equal.
    Sle,

    /// Unsigned less than or equal.
    Ule,

    /// Overflow.
    Of,

    /// No overflow.
    Nof,
}

impl fmt::Display for ConditionCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Eq => write!(f, "eq"),
            Self::Ne => write!(f, "ne"),
            Self::Slt => write!(f, "slt"),
            Self::Ult => write!(f, "ult"),
            Self::Sge => write!(f, "sge"),
            Self::Uge => write!(f, "uge"),
            Self::Sgt => write!(f, "sgt"),
            Self::Ugt => write!(f, "ugt"),
            Self::Sle => write!(f, "sle"),
            Self::Ule => write!(f, "ule"),
            Self::Of => write!(f, "of"),
            Self::Nof => write!(f, "nof"),
        }
    }
}
