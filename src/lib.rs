/*!

`peepmatic` is a DSL and compiler for generating peephole optimizers.

The user writes a set of optimizations in the DSL, and then `peepmatic` compiles
the set of optimizations into an efficient peephole optimizer.

 */

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]

mod ast;
mod automatize;
mod dot_fmt;
mod linear_passes;
mod linearize;
mod parser;
mod traversals;
mod verify;
pub use self::{
    ast::*, automatize::*, linear_passes::*, linearize::*, parser::*, traversals::*, verify::*,
};

use peepmatic_runtime::PeepholeOptimizations;
use std::fs;
use std::path::Path;

/// Compile the given DSL file into a compact peephole optimizations automaton!
///
/// ## Example
///
/// ```no_run
/// # fn main() -> anyhow::Result<()> {
/// use std::path::Path;
///
/// let peep_opts = peepmatic::compile_file(Path::new(
///     "path/to/optimizations.peepmatic"
/// ))?;
///
/// // Use the peephole optimizations or serialize them into bytes here...
/// # Ok(())
/// # }
/// ```
///
/// ## Visualizing the Peephole Optimizer's Automaton
///
/// To visualize (or debug) the peephole optimizer's automaton, set the
/// `PEEPMATIC_DOT` environment variable to a file path. A [GraphViz
/// Dot]((https://graphviz.gitlab.io/_pages/pdf/dotguide.pdf)) file showing the
/// peephole optimizer's automaton will be written to that file path.
pub fn compile_file(filename: &Path) -> anyhow::Result<PeepholeOptimizations> {
    let source = fs::read_to_string(filename)?;
    compile_str(&source, filename)
}

/// Compile the given DSL source text down into a compact peephole optimizations
/// automaton.
///
/// This is like [compile_file][crate::compile_file] but you bring your own file
/// I/O.
///
/// The `filename` parameter is used to provide better error messages.
///
/// ## Example
///
/// ```no_run
/// # fn main() -> anyhow::Result<()> {
/// use std::path::Path;
///
/// let peep_opts = peepmatic::compile_str(
///     "
///     (=> (iadd $x 0) $x)
///     (=> (imul $x 0) 0)
///     (=> (imul $x 1) $x)
///     ",
///     Path::new("my-optimizations"),
/// )?;
///
/// // Use the peephole optimizations or serialize them into bytes here...
/// # Ok(())
/// # }
/// ```
///
/// ## Visualizing the Peephole Optimizer's Automaton
///
/// To visualize (or debug) the peephole optimizer's automaton, set the
/// `PEEPMATIC_DOT` environment variable to a file path. A [GraphViz
/// Dot]((https://graphviz.gitlab.io/_pages/pdf/dotguide.pdf)) file showing the
/// peephole optimizer's automaton will be written to that file path.
pub fn compile_str(source: &str, filename: &Path) -> anyhow::Result<PeepholeOptimizations> {
    let buf = wast::parser::ParseBuffer::new(source).map_err(|mut e| {
        e.set_path(filename);
        e.set_text(source);
        e
    })?;

    let opts = wast::parser::parse::<Optimizations>(&buf).map_err(|mut e| {
        e.set_path(filename);
        e.set_text(source);
        e
    })?;

    verify(&opts).map_err(|mut e| {
        e.set_path(filename);
        e.set_text(source);
        e
    })?;

    let mut opts = crate::linearize(&opts);
    sort_least_to_most_general(&mut opts);
    match_in_same_order(&mut opts);
    insert_fallback_optimizations(&mut opts);
    sort_lexicographically(&mut opts);

    let automata = automatize(&opts);
    let paths = opts.paths;
    let integers = opts.integers;

    if let Ok(path) = std::env::var("PEEPMATIC_DOT") {
        let f = dot_fmt::PeepholeDotFmt(&paths, &integers);
        if let Err(e) = automata.write_dot_file(&f, &path) {
            panic!(
                "failed to write GraphViz Dot file to PEEPMATIC_DOT={}; error: {}",
                path, e
            );
        }
    }

    Ok(PeepholeOptimizations {
        paths,
        integers,
        automata,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_redundant_bor() {
        compile_file(Path::new("examples/redundant-bor.peepmatic")).unwrap();
    }

    #[test]
    fn compile_preopt() {
        compile_file(Path::new("examples/preopt.peepmatic")).unwrap();
    }
}
