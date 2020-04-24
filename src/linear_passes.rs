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
        ..
    } = opts;

    // NB: we *cannot* use an unstable sort here, because we want deterministic
    // compilation of optimizations to automata.
    optimizations.sort_by(|a, b| compare_optimization_generality(paths, a, b));
    debug_assert!(is_sorted_by_generality(opts));
}

/// Sort the linear optimizations lexicographically.
///
/// This sort order is required for automata construction.
pub fn sort_lexicographically(opts: &mut linear::Optimizations) {
    let linear::Optimizations {
        ref mut optimizations,
        ref paths,
        ..
    } = opts;

    // NB: we *cannot* use an unstable sort here, same as above.
    optimizations
        .sort_by(|a, b| compare_optimizations(paths, a, b, |a_len, b_len| a_len.cmp(&b_len)));
}

fn compare_optimizations(
    paths: &PathInterner,
    a: &linear::Optimization,
    b: &linear::Optimization,
    compare_lengths: impl Fn(usize, usize) -> Ordering,
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

    compare_lengths(a.increments.len(), b.increments.len())
}

fn compare_optimization_generality(
    paths: &PathInterner,
    a: &linear::Optimization,
    b: &linear::Optimization,
) -> Ordering {
    compare_optimizations(paths, a, b, |a_len, b_len| {
        // If they shared equivalent prefixes, then compare lengths and invert the
        // result because longer patterns are less general than shorter patterns.
        a_len.cmp(&b_len).reverse()
    })
}

fn compare_match_op_generality(
    paths: &PathInterner,
    a: linear::MatchOp,
    b: linear::MatchOp,
) -> Ordering {
    use linear::MatchOp::*;
    match (a, b) {
        (Opcode { path: a }, Opcode { path: b }) => compare_paths(paths, a, b),
        (Opcode { .. }, _) => Ordering::Less,
        (_, Opcode { .. }) => Ordering::Greater,

        (IntegerValue { path: a }, IntegerValue { path: b }) => compare_paths(paths, a, b),
        (IntegerValue { .. }, _) => Ordering::Less,
        (_, IntegerValue { .. }) => Ordering::Greater,

        (BooleanValue { path: a }, BooleanValue { path: b }) => compare_paths(paths, a, b),
        (BooleanValue { .. }, _) => Ordering::Less,
        (_, BooleanValue { .. }) => Ordering::Greater,

        (ConditionCode { path: a }, ConditionCode { path: b }) => compare_paths(paths, a, b),
        (ConditionCode { .. }, _) => Ordering::Less,
        (_, ConditionCode { .. }) => Ordering::Greater,

        (IsConst { path: a }, IsConst { path: b }) => compare_paths(paths, a, b),
        (IsConst { .. }, _) => Ordering::Less,
        (_, IsConst { .. }) => Ordering::Greater,

        (
            Eq {
                path_a: pa1,
                path_b: pb1,
            },
            Eq {
                path_a: pa2,
                path_b: pb2,
            },
        ) => compare_paths(paths, pa1, pa2).then(compare_paths(paths, pb1, pb2)),
        (Eq { .. }, _) => Ordering::Less,
        (_, Eq { .. }) => Ordering::Greater,

        (IsPowerOfTwo { path: a }, IsPowerOfTwo { path: b }) => compare_paths(paths, a, b),
        (IsPowerOfTwo { .. }, _) => Ordering::Less,
        (_, IsPowerOfTwo { .. }) => Ordering::Greater,

        (BitWidth { path: a }, BitWidth { path: b }) => compare_paths(paths, a, b),
        (BitWidth { .. }, _) => Ordering::Less,
        (_, BitWidth { .. }) => Ordering::Greater,

        (FitsInNativeWord { path: a }, FitsInNativeWord { path: b }) => compare_paths(paths, a, b),
        (FitsInNativeWord { .. }, _) => Ordering::Less,
        (_, FitsInNativeWord { .. }) => Ordering::Greater,

        (Nop, Nop) => Ordering::Equal,
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

/// Are the given optimizations sorted from least to most general?
pub(crate) fn is_sorted_by_generality(opts: &linear::Optimizations) -> bool {
    opts.optimizations
        .windows(2)
        .all(|w| compare_optimization_generality(&opts.paths, &w[0], &w[1]) <= Ordering::Equal)
}

/// Are the given optimizations sorted lexicographically?
pub(crate) fn is_sorted_lexicographically(opts: &linear::Optimizations) -> bool {
    opts.optimizations.windows(2).all(|w| {
        compare_optimizations(&opts.paths, &w[0], &w[1], |a_len, b_len| a_len.cmp(&b_len))
            <= Ordering::Equal
    })
}

/// Ensure that we emit match operations in a consistent order.
///
/// There are many linear optimizations, each of which have their own sequence
/// of match operations that need to be tested. But when interpreting the
/// automata against some instructions, we only perform a single sequence of
/// match operations, and at any given moment, we only want one match operation
/// to interpret next. This means that two optimizations that are next to each
/// other in the sorting must have their shared prefixes diverge on an
/// **expected result edge**, not on which match operation to preform next. And
/// if they have zero shared prefix, then we need to create one, that
/// immediately divereges on the expected result.
///
/// For example, consider these two patterns that don't have any shared prefix:
///
/// ```lisp
/// (=> (iadd $x $y) ...)
/// (=> $C ...)
/// ```
///
/// These produce the following linear match operations and expected results:
///
/// ```text
/// opcode @ 0 --iadd-->
/// is-const? @ 0 --true-->
/// ```
///
/// In order to ensure that we only have one match operation to interpret at any
/// given time when evaluating the automata, this pass transforms the second
/// optimization so that it shares a prefix match operation, but diverges on the
/// expected result:
///
/// ```text
/// opcode @ 0 --iadd-->
/// opcode @ 0 --(else)--> is-const? @ 0 --true-->
/// ```
pub fn match_in_same_order(opts: &mut linear::Optimizations) {
    assert!(!opts.optimizations.is_empty());

    let mut prefix = vec![];

    for opt in &mut opts.optimizations {
        assert!(!opt.increments.is_empty());

        let mut old_increments = opt.increments.iter().peekable();
        let mut new_increments = vec![];

        for (last_op, last_expected) in &prefix {
            match old_increments.peek() {
                None => {
                    break;
                }
                Some(inc) if *last_op == inc.operation => {
                    let inc = old_increments.next().unwrap();
                    new_increments.push(inc.clone());
                    if inc.expected != *last_expected {
                        break;
                    }
                }
                Some(_) => {
                    new_increments.push(linear::Increment {
                        operation: *last_op,
                        expected: None,
                        actions: vec![],
                    });
                    if last_expected.is_some() {
                        break;
                    }
                }
            }
        }

        new_increments.extend(old_increments.cloned());
        assert!(new_increments.len() >= opt.increments.len());
        opt.increments = new_increments;

        prefix.clear();
        prefix.extend(
            opt.increments
                .iter()
                .map(|inc| (inc.operation, inc.expected)),
        );
    }

    // Should still be sorted after this pass.
    debug_assert!(is_sorted_by_generality(&opts));
}

/// 99.99% of nops are unnecessary; remove them.
///
/// They're only needed for when a LHS pattern is just a variable, and that's
/// it. However, it is easier to have basically unused nop matching operations
/// for the DSL's edge-cases than it is to try and statically eliminate their
/// existence completely. So we just emit nop match operations for all variable
/// patterns, and then in this post-processing pass, we fuse them and their
/// actions with their preceding increment.
pub fn remove_unnecessary_nops(opts: &mut linear::Optimizations) {
    for opt in &mut opts.optimizations {
        if opt.increments.len() < 2 {
            debug_assert!(!opt.increments.is_empty());
            continue;
        }

        for i in (1..opt.increments.len()).rev() {
            if let linear::MatchOp::Nop = opt.increments[i].operation {
                let nop = opt.increments.remove(i);
                opt.increments[i - 1].actions.extend(nop.actions);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use linear::MatchOp::*;
    use peepmatic_runtime::{operator::Operator, paths::*};

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
                    mut integers,
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
                let mut i = |i: u64| Some(integers.intern(i).into());
                let expected = $make_expected(&mut p, &mut i);

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
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> Option<u32>| vec![
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Iadd as _)),
                (Nop, None),
                (Opcode { path: p(&[0, 1]) }, Some(Operator::Iadd as _)),
                (Nop, None),
                (Nop, None),
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Iadd as _)),
                (Nop, None),
                (IntegerValue { path: p(&[0, 1]) }, i(42))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Iadd as _)),
                (Nop, None),
                (IsConst { path: p(&[0, 1]) }, Some(1)),
                (IsPowerOfTwo { path: p(&[0, 1]) }, Some(1))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Iadd as _)),
                (Nop, None),
                (IsConst { path: p(&[0, 1]) }, Some(1)),
                (BitWidth { path: p(&[0, 0]) }, Some(32))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Iadd as _)),
                (Nop, None),
                (IsConst { path: p(&[0, 1]) }, Some(1))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Iadd as _)),
                (Nop, None),
                (
                    Eq {
                        path_a: p(&[0, 1]),
                        path_b: p(&[0, 0]),
                    },
                    Some(1)
                )
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Iadd as _)),
                (Nop, None),
                (Nop, None),
            ],
            vec![(Nop, None)]
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
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> Option<u32>| vec![
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Imul as _)),
                (IntegerValue { path: p(&[0, 0]) }, i(2)),
                (Nop, None)
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Imul as _)),
                (IntegerValue { path: p(&[0, 0]) }, i(1)),
                (Nop, None)
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Imul as _)),
                (Nop, None),
                (IntegerValue { path: p(&[0, 1]) }, i(2))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Imul as _)),
                (Nop, None),
                (IntegerValue { path: p(&[0, 1]) }, i(1))
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Iadd as _)),
                (IntegerValue { path: p(&[0, 0]) }, i(0)),
                (Nop, None)
            ],
            vec![
                (Opcode { path: p(&[0]) }, Some(Operator::Iadd as _)),
                (Nop, None),
                (IntegerValue { path: p(&[0, 1]) }, i(0))
            ]
        ]
    );
}
