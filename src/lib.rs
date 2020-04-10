/*!

`peepmatic` is a DSL and compiler for generating peephole optimizers.

The user writes a set of optimizations in the DSL, and then `peepmatic` compiles
the set of optimizations into an efficient peephole optimizer.

 */

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]

mod ast;
mod automatize;
mod linear_passes;
mod linearize;
mod parser;
mod traversals;
mod verify;
pub use self::{
    ast::*, automatize::*, linear_passes::*, linearize::*, parser::*, traversals::*, verify::*,
};
