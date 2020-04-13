//! Runtime support for `peepmatic`'s peephole optimizers.
//!
//! This crate contains everything required to use a `peepmatic`-generated
//! peephole optimizer.
//!
//! ## Why is this a different crate from `peepmatic`?
//!
//! In short: build times and code size.
//!
//! If you are just using a peephole optimizer, you shouldn't need the functions
//! to construct it from scratch from the DSL (and the implied code size and
//! compilation time), let alone even build it at all. You should just
//! deserialize an already-built peephole optimizer, and then use it.
//!
//! That's all that is contained here in this crate.

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]

pub mod integer_interner;
pub mod linear;
pub mod operator;
pub mod paths;

use peepmatic_automata::Automata;
use serde::{Deserialize, Serialize};

/// A peephole optimizer.
///
/// This is the compilation result of the `peepmatic` crate, after its taken a
/// bunch of optimizations written in the DSL and lowered and combined them.
#[derive(Debug, Serialize, Deserialize)]
pub struct PeepholeOptimizer {
    /// The instruction paths referenced by the peephole optimizer.
    pub paths: paths::PathInterner,

    /// Not all integers we're matching on fit in the `u32` that we use as the
    /// result of match operations. So we intern them and refer to them by id.
    pub integers: integer_interner::IntegerInterner,

    /// The underlying automata for matching optimizations' left-hand sides, and
    /// building up the corresponding right-hand side.
    pub automata: Automata<Option<u32>, linear::MatchOp, Vec<linear::Action>>,
}
