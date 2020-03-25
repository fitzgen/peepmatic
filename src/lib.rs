/*!

`peepmatic` is a DSL and compiler for generating peephole optimizers.

The user writes a set of optimizations in the DSL, and then `peepmatic` compiles
the set of optimizations into an efficient peephole optimizer.

 */

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]

mod ast;
mod parser;
mod traversals;
mod verify;
pub use self::{ast::*, parser::*, traversals::*, verify::*};
