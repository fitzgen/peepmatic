//! Compile a set of linear optimizations into an automata.

use peepmatic_automata::{Automata, Builder};
use peepmatic_runtime::linear;

/// Construct an automaton from a set of linear optimizations.
pub fn automatize(
    opts: &linear::Optimizations,
) -> Automata<Option<u32>, linear::MatchOp, Vec<linear::Action>> {
    debug_assert!(crate::linear_passes::is_sorted_lexicographically(opts));

    let mut builder = Builder::<Option<u32>, linear::MatchOp, Vec<linear::Action>>::new();

    for opt in &opts.optimizations {
        let mut insertion = builder.insert();
        for inc in &opt.increments {
            // Ensure that this state's associated data is this increment's
            // match operation.
            if let Some(op) = insertion.get_state_data() {
                assert_eq!(*op, inc.operation);
            } else {
                insertion.set_state_data(inc.operation);
            }

            insertion.next(inc.expected, inc.actions.clone());
        }
        insertion.finish();
    }

    builder.finish()
}
