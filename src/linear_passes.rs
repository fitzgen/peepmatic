//! Passes over the linear IR.

use peepmatic_runtime::{
    linear,
    paths::{PathId, PathInterner},
};
use std::cmp::Ordering;

/// Sort a set of optimizations from least to most general.
///
/// This helps us ensure that we always match the least-general (aka
/// most-specific) optimization that we can for a particular instruction
/// sequence.
///
/// For example, if we have both of these optimizations:
///
/// ```lisp
/// (=> (imul $C $x)
///     (imul_imm $C $x))
///
/// (=> (when (imul $C $x))
///           (is-power-of-two $C))
///     (ishl $x $C))
/// ```
///
/// and we are matching `(imul 4 (..))`, then we want to apply the second
/// optimization, because it is more specific than the first.
pub fn sort_least_to_most_general(opts: &mut linear::Optimizations) {
    let linear::Optimizations {
        ref mut optimizations,
        ref paths,
    } = opts;

    // NB: we *cannot* use an unstable sort here, because we want deterministic
    // compilation of optimizations to automata.
    optimizations.sort_by(|a, b| compare_optimization_generality(paths, a, b));
}

fn compare_optimization_generality(
    paths: &PathInterner,
    a: &linear::Optimization,
    b: &linear::Optimization,
) -> Ordering {
    for (a, b) in a.increments.iter().zip(b.increments.iter()) {
        let c = compare_match_op_generality(paths, a.operation, b.operation);
        if c != Ordering::Equal {
            return c;
        }

        let c = a.expected.cmp(&b.expected).reverse();
        if c != Ordering::Equal {
            return c;
        }
    }

    // If they shared equivalent prefixes, then compare lengths and invert the
    // result because longer patterns are less general than shorter patterns.
    a.increments.len().cmp(&b.increments.len()).reverse()
}

fn compare_match_op_generality(
    paths: &PathInterner,
    a: linear::MatchOp,
    b: linear::MatchOp,
) -> Ordering {
    match (a, b) {
        (linear::MatchOp::Opcode { path: a }, linear::MatchOp::Opcode { path: b }) => {
            compare_paths(paths, a, b)
        }
        (linear::MatchOp::Opcode { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::Opcode { .. }) => Ordering::Greater,

        (linear::MatchOp::IntegerValue { path: a }, linear::MatchOp::IntegerValue { path: b }) => {
            compare_paths(paths, a, b)
        }
        (linear::MatchOp::IntegerValue { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::IntegerValue { .. }) => Ordering::Greater,

        (linear::MatchOp::BooleanValue { path: a }, linear::MatchOp::BooleanValue { path: b }) => {
            compare_paths(paths, a, b)
        }
        (linear::MatchOp::BooleanValue { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::BooleanValue { .. }) => Ordering::Greater,

        (linear::MatchOp::IsConst { path: a }, linear::MatchOp::IsConst { path: b }) => {
            compare_paths(paths, a, b)
        }
        (linear::MatchOp::IsConst { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::IsConst { .. }) => Ordering::Greater,

        (
            linear::MatchOp::Eq {
                path: path_a,
                id: id_a,
            },
            linear::MatchOp::Eq {
                path: path_b,
                id: id_b,
            },
        ) => compare_paths(paths, path_a, path_b).then(id_a.cmp(&id_b)),
        (linear::MatchOp::Eq { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::Eq { .. }) => Ordering::Greater,

        (linear::MatchOp::IsPowerOfTwo { id: a }, linear::MatchOp::IsPowerOfTwo { id: b }) => {
            a.cmp(&b)
        }
        (linear::MatchOp::IsPowerOfTwo { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::IsPowerOfTwo { .. }) => Ordering::Greater,

        (linear::MatchOp::BitWidth { id: a }, linear::MatchOp::BitWidth { id: b }) => a.cmp(&b),
        (linear::MatchOp::BitWidth { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::BitWidth { .. }) => Ordering::Greater,

        (linear::MatchOp::Nop, _) => Ordering::Greater,
    }
}

fn compare_paths(paths: &PathInterner, a: PathId, b: PathId) -> Ordering {
    if a == b {
        Ordering::Equal
    } else {
        let a = paths.lookup(a);
        let b = paths.lookup(b);
        a.0.cmp(&b.0)
    }
}

/// Insert fallback optimizations for when we partially match one optimzation
/// that subsumes another, but then it doesn't work out.
///
/// Consider these optimization patterns:
///
/// ```lisp
/// (=> (iadd $w (iadd $x (iadd $y $z))) ...)
/// (=> (iadd $x $C)                     ...)
/// ```
///
/// These patterns get linearized into the following linear match operations and
/// expected values, followed by an implicit accept state that they end in:
///
/// ```text
/// Opcode@0 --iadd--> Opcode@0.1 --iadd--> Opcode@0.1.1 --iadd--> [Optimization 0]
/// Opcode@0 --iadd--> IsConst@0.1 --true--> [Optimization 1]
/// ```
///
/// If we naively combined these into an automata, first of all, it would be
/// nondeterministic because there are multiple states to move to after we find
/// that the root instruction's opcode is `iadd`. Secondly, if we inpect the
/// opcode of the root's second child (or its second child's second child) and
/// it is *not* an `iadd`, then we want to fallback to checking if it is a
/// constant, so that we can see if optimization 1 applies.
///
/// After this pass, the linear match operations and expected values would look
/// like:
///
/// ```text
/// Opcode@0 --iadd--> Opcode@0.1 --iadd--> Opcode@0.1.1 --iadd--> [Optimization 0]
/// Opcode@0 --iadd--> Opcode@0.1 --iadd--> Opcode@0.1.1 --else--> IsConst@0.1 --true--> [Optimization 1]
/// Opcode@0 --iadd--> Opcode@0.1 --else--> IsConst@0.1 --true--> [Optimization 1]
/// ```
///
/// Note that we no longer have transitions from one state into multiple other
/// states when given the same input. Also, we created a new linear match
/// sequence that accepts optimization 1 when the root's second child is an
/// `iadd` but the second child of the root's second child is not an `iadd` and
/// so optimization 0 cannot apply.
///
/// So ultimately, this pass is responsible for:
///
/// * Inserting "else" increments into a linear optimization where its match
///   operations diverge from the shared prefix with the previous optimization's
///   match operations. This ensures that the automata we build will be
///   deterministic, because we won't have any transitions to two different
///   states given the same expected result of a matching operation.
///
/// * Creating new optimizations that partially match the previous optimization,
///   but then fallback the current optimization.
///
/// The optimizations must already be sorted least-to-most general before
/// running this pass.
pub fn insert_fallback_optimizations(opts: &mut linear::Optimizations) {
    assert!(!opts.optimizations.is_empty());

    let mut new_opts = vec![opts.optimizations[0].clone()];

    for this_opt in &opts.optimizations[1..] {
        assert!(!this_opt.increments.is_empty());

        let last_opt_index = new_opts.len() - 1;
        let last_opt = &new_opts[last_opt_index];

        // Count how many inrements are in the shared prefix of this
        // optimization and the last (ignoring actions). That is, the increment
        // chains diverge at the `i`th increment.
        let i: usize = this_opt
            .increments
            .iter()
            .zip(last_opt.increments.iter())
            .take_while(|(a, b)| a.operation == b.operation && a.expected == b.expected)
            .map(|_| 1_usize)
            .sum();

        // Because the optimizations should already be sorted so that this
        // optimization is less specific than the last one, and more match
        // operations means an optimization is more specific, we cannot have the
        // last optimization's match operations be fully shared with this one.
        assert!(i < last_opt.increments.len());

        // When the divergence is only in the expected result, not in the
        // matching operation, then we don't need to insert any fallback
        // optimizations.
        if last_opt.increments[i].operation == this_opt.increments[i].operation {
            assert!(last_opt.increments[i].expected != this_opt.increments[i].expected);
            new_opts.push(this_opt.clone());
            continue;
        }

        for j in (i..last_opt.increments.len()).rev() {
            // Re-borrow here to avoid having an active borrow across the `push`
            // call below.
            let last_opt = &new_opts[last_opt_index];

            // Copy the shared prefix of increments.
            let mut increments = this_opt.increments[..i].to_vec();

            // Copy increments corresponding to the `j`th partial match of the
            // last optimization.
            increments.extend(
                last_opt.increments[i..=j]
                    .iter()
                    .map(|inc| linear::Increment {
                        operation: inc.operation,
                        expected: inc.expected,
                        actions: vec![],
                    }),
            );

            // But in case it doesn't fully match the last optimization, we add
            // an "else" edge back to this optimization.
            increments.last_mut().unwrap().expected = None;
            increments.extend(this_opt.increments[i..].iter().cloned());

            new_opts.push(linear::Optimization { increments });
        }
    }

    opts.optimizations = new_opts;

    // Re-sort to ensure that our new fallback optimizations and their edges are
    // still sorted for automata construction.
    sort_least_to_most_general(opts);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use linear::{LhsId, MatchOp::*};
    use peepmatic_runtime::paths::*;

    macro_rules! sorts_to {
        ($test_name:ident, $source:expr, $make_expected:expr) => {
            #[test]
            fn $test_name() {
                let buf = wast::parser::ParseBuffer::new($source).expect("should lex OK");

                let opts = match wast::parser::parse::<Optimizations>(&buf) {
                    Ok(opts) => opts,
                    Err(mut e) => {
                        e.set_path(std::path::Path::new(stringify!($test_name)));
                        e.set_text($source);
                        eprintln!("{}", e);
                        panic!("should parse OK")
                    }
                };

                if let Err(mut e) = crate::verify(&opts) {
                    e.set_path(std::path::Path::new(stringify!($test_name)));
                    e.set_text($source);
                    eprintln!("{}", e);
                    panic!("should verify OK")
                }

                let mut opts = crate::linearize(&opts);
                sort_least_to_most_general(&mut opts);

                let linear::Optimizations {
                    mut paths,
                    optimizations,
                } = opts;

                let actual: Vec<Vec<_>> = optimizations
                    .iter()
                    .map(|o| {
                        o.increments
                            .iter()
                            .map(|i| (i.operation, i.expected))
                            .collect()
                    })
                    .collect();

                let mut p = |p: &[u8]| paths.intern(Path::new(&p));
                let expected = $make_expected(&mut p);

                assert_eq!(expected, actual);
            }
        };
    }

    sorts_to!(
        test_sort_least_to_most_general,
        "
(=>       $x                                 0)
(=>       (iadd $x $y)                       0)
(=>       (iadd $x $x)                       0)
(=>       (iadd $x $C)                       0)
(=> (when (iadd $x $C) (is-power-of-two $C)) 0)
(=> (when (iadd $x $C) (bit-width $x 32))    0)
(=>       (iadd $x 42)                       0)
(=>       (iadd $x (iadd $y $z))             0)
",
        |p: &mut dyn FnMut(&[u8]) -> PathId| vec![
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (Opcode { path: p(&[0, 1]) }, Some(2))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (IntegerValue { path: p(&[0, 1]) }, Some(42))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (IsConst { path: p(&[0, 1]) }, Some(1)),
                (IsPowerOfTwo { id: LhsId(1) }, Some(1))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (IsConst { path: p(&[0, 1]) }, Some(1)),
                (BitWidth { id: LhsId(0) }, Some(32))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (IsConst { path: p(&[0, 1]) }, Some(1))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (
                    Eq {
                        id: LhsId(0),
                        path: p(&[0, 1])
                    },
                    Some(1)
                )
            ],
            vec![(Opcode { path: p(&[0]) }, Some(2))],
            vec![(Nop, None)]
        ]
    );

    macro_rules! test_fallback_insertion {
        ($test_name:ident, $source:expr, $make_expected:expr) => {
            #[test]
            fn $test_name() {
                let buf = wast::parser::ParseBuffer::new($source).expect("should lex OK");

                let opts = match wast::parser::parse::<Optimizations>(&buf) {
                    Ok(opts) => opts,
                    Err(mut e) => {
                        e.set_path(std::path::Path::new(stringify!($test_name)));
                        e.set_text($source);
                        eprintln!("{}", e);
                        panic!("should parse OK")
                    }
                };

                if let Err(mut e) = crate::verify(&opts) {
                    e.set_path(std::path::Path::new(stringify!($test_name)));
                    e.set_text($source);
                    eprintln!("{}", e);
                    panic!("should verify OK")
                }

                let mut opts = crate::linearize(&opts);
                sort_least_to_most_general(&mut opts);
                insert_fallback_optimizations(&mut opts);

                let actual: Vec<Vec<_>> = opts
                    .optimizations
                    .iter()
                    .map(|o| {
                        o.increments
                            .iter()
                            .map(|i| (i.operation, i.expected))
                            .collect()
                    })
                    .collect();
                let expected = $make_expected(&mut |p| opts.paths.intern(Path::new(&p)));
                assert_eq!(expected, actual);
            }
        };
    }

    test_fallback_insertion!(
        test_insert_fallback_optimizations,
        "
(=> (iadd $w (iadd $x (iadd $y $z))) 0)
(=> (iadd $x $C)                     0)
",
        |p: &mut dyn FnMut(&[u8]) -> PathId| vec![
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (Opcode { path: p(&[0, 1]) }, Some(2)),
                (
                    Opcode {
                        path: p(&[0, 1, 1]),
                    },
                    Some(2)
                ),
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (Opcode { path: p(&[0, 1]) }, Some(2)),
                (
                    Opcode {
                        path: p(&[0, 1, 1])
                    },
                    None
                ),
                (IsConst { path: p(&[0, 1]) }, Some(1)),
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (Opcode { path: p(&[0, 1]) }, None),
                (IsConst { path: p(&[0, 1]) }, Some(1)),
            ],
        ]
    );

    sorts_to!(
        expected_edges_are_sorted,
        "
(=> (iadd 0 $x) $x)
(=> (iadd $x 0) $x)
(=> (imul 1 $x) $x)
(=> (imul $x 1) $x)
(=> (imul 2 $x) (ishl $x 1))
(=> (imul $x 2) (ishl $x 1))
",
        |p: &mut dyn FnMut(&[u8]) -> PathId| vec![
            vec![
                (Opcode { path: p(&[0]) }, Some(5)),
                (IntegerValue { path: p(&[0, 0]) }, Some(2))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(5)),
                (IntegerValue { path: p(&[0, 0]) }, Some(1)),
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(5)),
                (IntegerValue { path: p(&[0, 1]) }, Some(2))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(5)),
                (IntegerValue { path: p(&[0, 1]) }, Some(1)),
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (IntegerValue { path: p(&[0, 0]) }, Some(0)),
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (IntegerValue { path: p(&[0, 1]) }, Some(0)),
            ],
        ]
    );

    test_fallback_insertion!(
        no_fallback_insertion_when_divergence_is_at_same_operation_but_different_expected_result,
        "
(=> 0 0)
(=> 1 1)
(=> 2 2)
(=> 3 3)
(=> 4 4)
(=> 5 5)
",
        |p: &mut dyn FnMut(&[u8]) -> PathId| vec![
            vec![(IntegerValue { path: p(&[0]) }, Some(5))],
            vec![(IntegerValue { path: p(&[0]) }, Some(4))],
            vec![(IntegerValue { path: p(&[0]) }, Some(3))],
            vec![(IntegerValue { path: p(&[0]) }, Some(2))],
            vec![(IntegerValue { path: p(&[0]) }, Some(1))],
            vec![(IntegerValue { path: p(&[0]) }, Some(0))],
        ]
    );

    test_fallback_insertion!(
        no_fallbacks_after_same_op_with_different_expected_results_with_long_tail,
        "
(=> (iadd 1 (iadd $x (iadd $y $z))) 0)
(=> (iadd 0 $C) 0)
",
        |p: &mut dyn FnMut(&[u8]) -> PathId| vec![
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (IntegerValue { path: p(&[0, 0]) }, Some(1)),
                (Opcode { path: p(&[0, 1]) }, Some(2)),
                (
                    Opcode {
                        path: p(&[0, 1, 1])
                    },
                    Some(2)
                )
            ],
            // Note: no fallbacks inserted here because they branch on different
            // integer values.
            vec![
                (Opcode { path: p(&[0]) }, Some(2)),
                (IntegerValue { path: p(&[0, 0]) }, Some(0)),
                (IsConst { path: p(&[0, 1]) }, Some(1))
            ]
        ]
    );
}