//! Types.

use serde::{Deserialize, Serialize};
use std::fmt;

/// An ascribed type for an operation or operator.
#[allow(missing_docs)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    B1,
    B8,
    B16,
    B32,
    B64,
    B128,
    I1,
    I8,
    I16,
    I32,
    I64,
    I128,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_int() {
            write!(f, "i")?;
        } else {
            debug_assert!(self.is_bool());
            write!(f, "b")?;
        }
        write!(f, "{}", self.bit_width())
    }
}

impl Type {
    /// Get the bit width of this type.
    pub fn bit_width(&self) -> u8 {
        match self {
            Self::B1 | Self::I1 => 1,
            Self::B8 | Self::I8 => 8,
            Self::B16 | Self::I16 => 16,
            Self::B32 | Self::I32 => 32,
            Self::B64 | Self::I64 => 64,
            Self::B128 | Self::I128 => 128,
        }
    }

    /// Is this a boolean type?
    pub fn is_bool(&self) -> bool {
        match self {
            Self::B1 | Self::B8 | Self::B16 | Self::B32 | Self::B64 | Self::B128 => true,
            _ => false,
        }
    }

    /// Is this an integer type?
    pub fn is_int(&self) -> bool {
        match self {
            Self::I1 | Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::I128 => true,
            _ => false,
        }
    }
}

#[cfg(feature = "construct")]
mod tok {
    use wast::custom_keyword;
    custom_keyword!(b1);
    custom_keyword!(b8);
    custom_keyword!(b16);
    custom_keyword!(b32);
    custom_keyword!(b64);
    custom_keyword!(b128);
    custom_keyword!(i1);
    custom_keyword!(i8);
    custom_keyword!(i16);
    custom_keyword!(i32);
    custom_keyword!(i64);
    custom_keyword!(i128);
}

#[cfg(feature = "construct")]
impl<'a> wast::parser::Parse<'a> for Type {
    fn parse(p: wast::parser::Parser<'a>) -> wast::parser::Result<Self> {
        if p.peek::<tok::b1>() {
            p.parse::<tok::b1>()?;
            return Ok(Type::B1);
        }
        if p.peek::<tok::b8>() {
            p.parse::<tok::b8>()?;
            return Ok(Type::B8);
        }
        if p.peek::<tok::b16>() {
            p.parse::<tok::b16>()?;
            return Ok(Type::B16);
        }
        if p.peek::<tok::b32>() {
            p.parse::<tok::b32>()?;
            return Ok(Type::B32);
        }
        if p.peek::<tok::b64>() {
            p.parse::<tok::b64>()?;
            return Ok(Type::B64);
        }
        if p.peek::<tok::b128>() {
            p.parse::<tok::b128>()?;
            return Ok(Type::B128);
        }
        if p.peek::<tok::i1>() {
            p.parse::<tok::i1>()?;
            return Ok(Type::I1);
        }
        if p.peek::<tok::i8>() {
            p.parse::<tok::i8>()?;
            return Ok(Type::I8);
        }
        if p.peek::<tok::i16>() {
            p.parse::<tok::i16>()?;
            return Ok(Type::I16);
        }
        if p.peek::<tok::i32>() {
            p.parse::<tok::i32>()?;
            return Ok(Type::I32);
        }
        if p.peek::<tok::i64>() {
            p.parse::<tok::i64>()?;
            return Ok(Type::I64);
        }
        if p.peek::<tok::i128>() {
            p.parse::<tok::i128>()?;
            return Ok(Type::I128);
        }
        Err(p.error("expected an ascribed type"))
    }
}
