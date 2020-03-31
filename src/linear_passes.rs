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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

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

        let mut p = |path: &[u8]| paths.intern(peepmatic_runtime::paths::Path::new(&path));

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
}
