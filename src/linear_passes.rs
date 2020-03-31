//! Passes over the linear IR.

use peepmatic_runtime::linear;
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
    // NB: we *cannot* use an unstable sort here, because we want deterministic
    // compilation of optimizations to automata.
    opts.optimizations.sort_by(compare_optimization_generality);
}

fn compare_optimization_generality(a: &linear::Optimization, b: &linear::Optimization) -> Ordering {
    for (a, b) in a.increments.iter().zip(b.increments.iter()) {
        let c = compare_match_op_generality(a.operation, b.operation);
        if c != Ordering::Equal {
            return c;
        }
    }

    // If they shared equivalent prefixes, then compare lengths and invert the
    // result because longer patterns are less general than shorter patterns.
    a.increments.len().cmp(&b.increments.len()).reverse()
}

fn compare_match_op_generality(a: linear::MatchOp, b: linear::MatchOp) -> Ordering {
    match (a, b) {
        (a, b) if a == b => Ordering::Equal,

        (linear::MatchOp::Opcode { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::Opcode { .. }) => Ordering::Greater,

        (linear::MatchOp::IntegerValue { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::IntegerValue { .. }) => Ordering::Greater,

        (linear::MatchOp::BooleanValue { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::BooleanValue { .. }) => Ordering::Greater,

        (linear::MatchOp::IsConst { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::IsConst { .. }) => Ordering::Greater,

        (linear::MatchOp::Eq { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::Eq { .. }) => Ordering::Greater,

        (linear::MatchOp::IsPowerOfTwo { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::IsPowerOfTwo { .. }) => Ordering::Greater,

        (linear::MatchOp::BitWidth { .. }, _) => Ordering::Less,
        (_, linear::MatchOp::BitWidth { .. }) => Ordering::Greater,

        (linear::MatchOp::Nop, _) => Ordering::Greater,
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

        // Count how many match operations are in the shared prefix of this
        // optimization and the last. That is, the match operations diverge at
        // the `i`th increment.
        let i: usize = this_opt
            .increments
            .iter()
            .zip(last_opt.increments.iter())
            .take_while(|(a, b)| a.operation == b.operation)
            .map(|_| 1_usize)
            .sum();

        // Because the optimizations should already be sorted so that this
        // optimization is less specific than the last one, and more match
        // operations means an optimization is more specific, we cannot have the
        // last optimization's match operations be fully shared with this one.
        assert!(i < last_opt.increments.len());

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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use linear::MatchOp::*;
    use peepmatic_runtime::paths::*;

    #[test]
    fn test_sort_least_to_most_general() {
        let source = "
(=>       $x                                 0)
(=>       (iadd $x $y)                       0)
(=>       (iadd $x $x)                       0)
(=>       (iadd $x $C)                       0)
(=> (when (iadd $x $C) (is-power-of-two $C)) 0)
(=> (when (iadd $x $C) (bit-width $x 32))    0)
(=>       (iadd $x 42)                       0)
(=>       (iadd $x (iadd $y $z))             0)
";

        let buf = wast::parser::ParseBuffer::new(source).expect("should lex OK");

        let opts = match wast::parser::parse::<Optimizations>(&buf) {
            Ok(opts) => opts,
            Err(mut e) => {
                e.set_path(std::path::Path::new("test_sort_least_to_most_general"));
                e.set_text(source);
                eprintln!("{}", e);
                panic!("should parse OK")
            }
        };

        if let Err(mut e) = crate::verify(&opts) {
            e.set_path(std::path::Path::new("test_sort_least_to_most_general"));
            e.set_text(source);
            eprintln!("{}", e);
            panic!("should verify OK")
        }

        let mut opts = crate::linearize(&opts);

        assert_eq!(opts.optimizations.len(), 8);
        sort_least_to_most_general(&mut opts);
        assert_eq!(opts.optimizations.len(), 8);

        let linear::Optimizations {
            mut paths,
            optimizations,
        } = opts;

        dbg!(&optimizations);

        fn match_ops(opt: &linear::Optimization) -> Vec<linear::MatchOp> {
            opt.increments.iter().map(|i| i.operation).collect()
        }

        let mut p = |path: &[u8]| paths.intern(Path::new(&path));

        assert_eq!(
            match_ops(&optimizations[0]),
            vec![
                linear::MatchOp::Opcode { path: p(&[0]) },
                linear::MatchOp::Opcode { path: p(&[0, 1]) },
            ],
        );

        assert_eq!(
            match_ops(&optimizations[1]),
            vec![
                linear::MatchOp::Opcode { path: p(&[0]) },
                linear::MatchOp::IntegerValue { path: p(&[0, 1]) },
            ],
        );

        assert_eq!(
            match_ops(&optimizations[2]),
            vec![
                linear::MatchOp::Opcode { path: p(&[0]) },
                linear::MatchOp::IsConst { path: p(&[0, 1]) },
                linear::MatchOp::IsPowerOfTwo {
                    id: linear::LhsId(1),
                },
            ],
        );

        assert_eq!(
            match_ops(&optimizations[3]),
            vec![
                linear::MatchOp::Opcode { path: p(&[0]) },
                linear::MatchOp::IsConst { path: p(&[0, 1]) },
                linear::MatchOp::BitWidth {
                    id: linear::LhsId(0),
                },
            ],
        );

        assert_eq!(
            match_ops(&optimizations[4]),
            vec![
                linear::MatchOp::Opcode { path: p(&[0]) },
                linear::MatchOp::IsConst { path: p(&[0, 1]) },
            ],
        );

        assert_eq!(
            match_ops(&optimizations[5]),
            vec![
                linear::MatchOp::Opcode { path: p(&[0]) },
                linear::MatchOp::Eq {
                    id: linear::LhsId(0),
                    path: p(&[0, 1]),
                },
            ],
        );

        assert_eq!(
            match_ops(&optimizations[6]),
            vec![linear::MatchOp::Opcode { path: p(&[0]) }],
        );

        assert_eq!(match_ops(&optimizations[7]), vec![linear::MatchOp::Nop]);
    }

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
}
