//! Convert an AST into its linear equivalent.
//!
//! Convert each optimization's left-hand side into a linear series of match
//! operations. This makes it easy to create an automaton, because automatas
//! typically deal with a linear sequence of inputs. The optimization's
//! right-hand side is built incrementally inside actions that are taken on
//! transitions between match operations.
//!
//! See `crates/runtime/src/linear.rs` for the linear datatype definitions.
//!
//! ## Example
//!
//! As an example, if we linearize this optimization:
//!
//! ```lisp
//! (=> (when (imul $x $C)
//!           (is-power-of-two $C))
//!     (ishl $x $(log2 C)))
//! ```
//!
//! Then we should get the following linear chain of "increments":
//!
//! ```ignore
//! [
//!   // ( Match Operation, Expected Value, Actions )
//!   ( Opcode@0,           imul,           [$x = GetLhs@0.0, $C = GetLhs@0.1, ...] ),
//!   ( IsConst(C),         true,           [] ),
//!   ( IsPowerOfTwo(C),    true,           [] ),
//! ]
//! ```
//!
//! Each increment will essentially become a state and a transition out of that
//! state in the final automata, along with the actions to perform when taking
//! that transition. The actions record the scope of matches from the left-hand
//! side and also incrementally build the right-hand side's instructions. (Note
//! that we've elided the actions that build up the optimization's right-hand
//! side in this example.)
//!
//! ## General Principles
//!
//! Here are the general principles that linearization should adhere to:
//!
//! * Actions should be pushed as early in the optimization's increment chain as
//!   they can be. This means the tail has fewer side effects, and is therefore
//!   more likely to be share-able with other optimizations in the automata that
//!   we build.
//!
//! * RHS actions cannot reference matches from the LHS until they've been
//!   defined. And finally, an RHS operation's operands must be defined before
//!   the RHS operation itself. In general, definitions must come before uses!
//!
//! * Shorter increment chains are better! This means fewer tests when matching
//!   left-hand sides, and a more-compact, more-cache-friendly automata, and
//!   ultimately, a faster automata.
//!
//! * An increment's match operation should be a switch rather than a predicate
//!   that returns a boolean. For example, we switch on an instruction's opcode,
//!   rather than ask whether this operation is an `imul`. This allows for more
//!   prefix sharing in the automata, which (again) makes it more compact and
//!   more cache friendly.
//!
//! ## Implementation Overview
//!
//! We emit match operations for a left-hand side's pattern structure, followed
//! by match operations for its preconditions on that structure. This ensures
//! that anything bound in the pattern is defined before it is used in
//! precondition.
//!
//! Within matching the pattern structure, we emit matching operations in a
//! pre-order traversal of the pattern. This ensures that we've already matched
//! an operation before we consider its operands, and therefore we already know
//! the operands exist. See `PatternPreOrder` for details.
//!
//! As we define the match operations for a pattern, we remember the path where
//! each LHS id first occurred. These will later be reused when building the RHS
//! actions. See `LhsIdToPath` for details.
//!
//! After we've generated the match operations and expected result of those
//! match operations, then we generate the right-hand side actions. The
//! right-hand side is built up a post-order traversal, so that operands are
//! defined before they are used. See `RhsPostOrder` and `RhsBuilder` for
//! details.
//!
//! Finally, see `linearize_optimization` for the the main AST optimization into
//! linear optimization translation function.

use crate::ast::*;
use crate::traversals::Dfs;
use peepmatic_runtime::{
    integer_interner::IntegerInterner,
    linear,
    paths::{Path, PathId, PathInterner},
};
use std::collections::BTreeMap;
use wast::Id;

/// Translate the given AST optimizations into linear optimizations.
pub fn linearize(opts: &Optimizations) -> linear::Optimizations {
    let mut optimizations = vec![];
    let mut paths = PathInterner::new();
    let mut integers = IntegerInterner::new();
    for opt in &opts.optimizations {
        let lin_opt = linearize_optimization(&mut paths, &mut integers, opt);
        optimizations.push(lin_opt);
    }
    linear::Optimizations {
        optimizations,
        paths,
        integers,
    }
}

/// Translate an AST optimization into a linear optimization!
fn linearize_optimization(
    paths: &mut PathInterner,
    integers: &mut IntegerInterner,
    opt: &Optimization,
) -> linear::Optimization {
    let mut increments: Vec<linear::Increment> = vec![];

    let mut lhs_id_to_path = LhsIdToPath::new();

    // We do a pre-order traversal of the LHS because we don't know whether a
    // child actually exists to match on until we've matched its parent, and we
    // don't want to emit matching operations on things that might not exist!
    let mut patterns = PatternPreOrder::new(&opt.lhs.pattern);
    while let Some((path, pattern)) = patterns.next(paths) {
        // Create the matching parts of an `Increment` for this part of the
        // pattern, without any actions yet.
        let (operation, expected) = pattern.to_linear_match_op(integers, &lhs_id_to_path, path);
        increments.push(linear::Increment {
            operation,
            expected,
            actions: vec![],
        });

        lhs_id_to_path.remember_path_to_pattern_ids(pattern, path);

        // Some operations require type ascriptions for us to infer the correct
        // bit width of their results: `ireduce`, `sextend`, `uextend`, etc.
        // When there is such a type ascription in the pattern, insert another
        // increment that checks the instruction-being-matched's bit width.
        if let Pattern::Operation(Operation { r#type, .. }) = pattern {
            if let Some(w) = r#type.get().and_then(|ty| ty.bit_width.fixed_width()) {
                increments.push(linear::Increment {
                    operation: linear::MatchOp::BitWidth { path },
                    expected: Some(w as u32),
                    actions: vec![],
                });
            }
        }
    }

    // Now that we've added all the increments for the LHS pattern, add the
    // increments for its preconditions.
    for pre in &opt.lhs.preconditions {
        increments.push(pre.to_linear_increment(&lhs_id_to_path));
    }

    assert!(!increments.is_empty());

    // Finally, generate the RHS-building actions and attach them to the first increment.
    let mut rhs_builder = RhsBuilder::new(&opt.rhs);
    rhs_builder.add_rhs_build_actions(integers, &lhs_id_to_path, &mut increments[0].actions);

    linear::Optimization { increments }
}

/// A post-order, depth-first traversal of right-hand sides.
///
/// Does not maintain any extra state about the traversal, such as where in the
/// tree each yielded node comes from.
struct RhsPostOrder<'a> {
    dfs: Dfs<'a>,
}

impl<'a> RhsPostOrder<'a> {
    fn new(rhs: &'a Rhs<'a>) -> Self {
        Self { dfs: Dfs::new(rhs) }
    }
}

impl<'a> Iterator for RhsPostOrder<'a> {
    type Item = &'a Rhs<'a>;

    fn next(&mut self) -> Option<&'a Rhs<'a>> {
        use crate::traversals::TraversalEvent as TE;
        loop {
            match self.dfs.next()? {
                (TE::Exit, DynAstRef::Rhs(rhs)) => return Some(rhs),
                _ => continue,
            }
        }
    }
}

/// A pre-order, depth-first traversal of left-hand side patterns.
///
/// Keeps track of the path to each pattern, and yields it along side the
/// pattern AST node.
struct PatternPreOrder<'a> {
    last_child: Option<u8>,
    path: Vec<u8>,
    dfs: Dfs<'a>,
}

impl<'a> PatternPreOrder<'a> {
    fn new(pattern: &'a Pattern<'a>) -> Self {
        Self {
            last_child: None,
            path: vec![],
            dfs: Dfs::new(pattern),
        }
    }

    fn next(&mut self, paths: &mut PathInterner) -> Option<(PathId, &'a Pattern<'a>)> {
        use crate::traversals::TraversalEvent as TE;
        loop {
            match self.dfs.next()? {
                (TE::Enter, DynAstRef::Pattern(pattern)) => {
                    let last_child = self.last_child.take();
                    self.path.push(match last_child {
                        None => 0,
                        Some(c) => {
                            assert!(
                                c < std::u8::MAX,
                                "operators must have less than or equal u8::MAX arity"
                            );
                            c + 1
                        }
                    });
                    let path = paths.intern(Path(&self.path));
                    return Some((path, pattern));
                }
                (TE::Exit, DynAstRef::Pattern(_)) => {
                    self.last_child = Some(
                        self.path
                            .pop()
                            .expect("should always have a non-empty path during traversal"),
                    );
                }
                _ => {}
            }
        }
    }
}

/// A map from left-hand side identifiers to the path in the left-hand side
/// where they first occurred.
struct LhsIdToPath<'a> {
    id_to_path: BTreeMap<&'a str, PathId>,
}

impl<'a> LhsIdToPath<'a> {
    /// Construct a new, empty `LhsIdToPath`.
    fn new() -> Self {
        Self {
            id_to_path: Default::default(),
        }
    }

    /// Have we already seen the given identifier?
    fn get_first_occurrence(&self, id: &Id) -> Option<PathId> {
        self.id_to_path.get(id.name()).copied()
    }

    /// Get the path within the left-hand side pattern where we first saw the
    /// given AST id.
    ///
    /// ## Panics
    ///
    /// Panics if the given AST id has not already been canonicalized.
    fn unwrap_first_occurrence(&self, id: &Id) -> PathId {
        self.id_to_path[id.name()]
    }

    /// Remember the path to any LHS ids used in the given pattern.
    fn remember_path_to_pattern_ids(&mut self, pattern: &'a Pattern<'a>, path: PathId) {
        match pattern {
            // If this is the first time we've seen an identifier defined on the
            // left-hand side, remember it.
            Pattern::Variable(Variable { id, .. }) | Pattern::Constant(Constant { id, .. }) => {
                self.id_to_path.entry(id.name()).or_insert(path);
            }
            _ => {}
        }
    }
}

/// An `RhsBuilder` emits the actions for building the right-hand side
/// instructions.
struct RhsBuilder<'a> {
    // We do a post order traversal of the RHS because an RHS instruction cannot
    // be created until after all of its operands are created.
    rhs_post_order: RhsPostOrder<'a>,

    // A map from a right-hand side's span to its `linear::RhsId`. This is used
    // by RHS-construction actions to reference operands. In practice the
    // `RhsId` is roughly equivalent to its index in the post-order traversal of
    // the RHS.
    rhs_span_to_id: BTreeMap<wast::Span, linear::RhsId>,
}

impl<'a> RhsBuilder<'a> {
    /// Create a new builder for the given right-hand side.
    fn new(rhs: &'a Rhs<'a>) -> Self {
        let rhs_post_order = RhsPostOrder::new(rhs);
        let rhs_span_to_id = Default::default();
        Self {
            rhs_post_order,
            rhs_span_to_id,
        }
    }

    /// Get the `linear::RhsId` for the given right-hand side.
    ///
    /// ## Panics
    ///
    /// Panics if we haven't already emitted the action for building this RHS's
    /// instruction.
    fn get_rhs_id(&self, rhs: &Rhs) -> linear::RhsId {
        self.rhs_span_to_id[&rhs.span()]
    }

    /// Create actions for building up this right-hand side of an optimization.
    ///
    /// Because we are walking the right-hand side with a post-order traversal,
    /// we know that we already created an instruction's operands that are
    /// defined in the right-hand side, before we get to the parent instruction.
    fn add_rhs_build_actions(
        &mut self,
        integers: &mut IntegerInterner,
        lhs_id_to_path: &LhsIdToPath,
        actions: &mut Vec<linear::Action>,
    ) {
        while let Some(rhs) = self.rhs_post_order.next() {
            actions.push(self.rhs_to_linear_action(integers, lhs_id_to_path, rhs));
            let id = linear::RhsId(self.rhs_span_to_id.len() as u32);
            self.rhs_span_to_id.insert(rhs.span(), id);
        }
    }

    fn rhs_to_linear_action(
        &self,
        integers: &mut IntegerInterner,
        lhs_id_to_path: &LhsIdToPath,
        rhs: &Rhs,
    ) -> linear::Action {
        match rhs {
            Rhs::ValueLiteral(ValueLiteral::Integer(i)) => linear::Action::MakeIntegerConst {
                value: integers.intern(i.value as u64),
                bit_width: i
                    .bit_width
                    .get()
                    .expect("should be initialized after type checking"),
            },
            Rhs::ValueLiteral(ValueLiteral::Boolean(b)) => linear::Action::MakeBooleanConst {
                value: b.value,
                bit_width: b
                    .bit_width
                    .get()
                    .expect("should be initialized after type checking"),
            },
            Rhs::ValueLiteral(ValueLiteral::ConditionCode(ConditionCode { cc, .. })) => {
                linear::Action::MakeConditionCode { cc: *cc }
            }
            Rhs::Variable(Variable { id, .. }) | Rhs::Constant(Constant { id, .. }) => {
                let path = lhs_id_to_path.unwrap_first_occurrence(id);
                linear::Action::GetLhs { path }
            }
            Rhs::Unquote(unq) => match unq.operands.len() {
                1 => linear::Action::UnaryUnquote {
                    operator: unq.operator,
                    operand: self.get_rhs_id(&unq.operands[0]),
                },
                2 => linear::Action::BinaryUnquote {
                    operator: unq.operator,
                    operands: [
                        self.get_rhs_id(&unq.operands[0]),
                        self.get_rhs_id(&unq.operands[1]),
                    ],
                },
                n => unreachable!("no unquote operators of arity {}", n),
            },
            Rhs::Operation(op) => match op.operands.len() {
                1 => linear::Action::MakeUnaryInst {
                    operator: op.operator,
                    r#type: op
                        .r#type
                        .get()
                        .expect("should be initialized after type checking"),
                    operand: self.get_rhs_id(&op.operands[0]),
                },
                2 => linear::Action::MakeBinaryInst {
                    operator: op.operator,
                    r#type: op
                        .r#type
                        .get()
                        .expect("should be initialized after type checking"),
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                    ],
                },
                3 => linear::Action::MakeTernaryInst {
                    operator: op.operator,
                    r#type: op
                        .r#type
                        .get()
                        .expect("should be initialized after type checking"),
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                        self.get_rhs_id(&op.operands[2]),
                    ],
                },
                n => unreachable!("no instructions of arity {}", n),
            },
        }
    }
}

impl Precondition<'_> {
    /// Convert this precondition into a `linear::Increment`.
    fn to_linear_increment(&self, lhs_id_to_path: &LhsIdToPath) -> linear::Increment {
        match self.constraint {
            Constraint::IsPowerOfTwo => {
                let id = match &self.operands[0] {
                    ConstraintOperand::Constant(Constant { id, .. }) => id,
                    _ => unreachable!("checked in verification"),
                };
                let path = lhs_id_to_path.unwrap_first_occurrence(&id);
                linear::Increment {
                    operation: linear::MatchOp::IsPowerOfTwo { path },
                    expected: Some(1),
                    actions: vec![],
                }
            }
            Constraint::BitWidth => {
                let id = match &self.operands[0] {
                    ConstraintOperand::Constant(Constant { id, .. })
                    | ConstraintOperand::Variable(Variable { id, .. }) => id,
                    _ => unreachable!("checked in verification"),
                };
                let path = lhs_id_to_path.unwrap_first_occurrence(&id);

                let width = match &self.operands[1] {
                    ConstraintOperand::ValueLiteral(ValueLiteral::Integer(Integer {
                        value,
                        ..
                    })) => *value,
                    _ => unreachable!("checked in verification"),
                };
                debug_assert!(width <= 128);
                debug_assert!((width as u8).is_power_of_two());

                linear::Increment {
                    operation: linear::MatchOp::BitWidth { path },
                    expected: Some(width as u32),
                    actions: vec![],
                }
            }
            Constraint::FitsInNativeWord => {
                let id = match &self.operands[0] {
                    ConstraintOperand::Constant(Constant { id, .. })
                    | ConstraintOperand::Variable(Variable { id, .. }) => id,
                    _ => unreachable!("checked in verification"),
                };
                let path = lhs_id_to_path.unwrap_first_occurrence(&id);
                linear::Increment {
                    operation: linear::MatchOp::FitsInNativeWord { path },
                    expected: Some(1),
                    actions: vec![],
                }
            }
        }
    }
}

impl Pattern<'_> {
    /// Convert this pattern into its linear match operation and the expected
    /// result of that operation.
    ///
    /// NB: these mappings to expected values need to stay sync'd with the
    /// runtime!
    fn to_linear_match_op(
        &self,
        integers: &mut IntegerInterner,
        lhs_id_to_path: &LhsIdToPath,
        path: PathId,
    ) -> (linear::MatchOp, Option<u32>) {
        match self {
            Pattern::ValueLiteral(ValueLiteral::Integer(Integer { value, .. })) => (
                linear::MatchOp::IntegerValue { path },
                Some(integers.intern(*value as u64).into()),
            ),
            Pattern::ValueLiteral(ValueLiteral::Boolean(Boolean { value, .. })) => {
                (linear::MatchOp::BooleanValue { path }, Some(*value as u32))
            }
            Pattern::ValueLiteral(ValueLiteral::ConditionCode(ConditionCode { cc, .. })) => {
                (linear::MatchOp::ConditionCode { path }, Some(*cc as u32))
            }
            Pattern::Constant(Constant { id, .. }) => {
                if let Some(path_b) = lhs_id_to_path.get_first_occurrence(id) {
                    debug_assert!(path != path_b);
                    (
                        linear::MatchOp::Eq {
                            path_a: path,
                            path_b,
                        },
                        Some(1),
                    )
                } else {
                    (linear::MatchOp::IsConst { path }, Some(1))
                }
            }
            Pattern::Variable(Variable { id, .. }) => {
                if let Some(path_b) = lhs_id_to_path.get_first_occurrence(id) {
                    debug_assert!(path != path_b);
                    (
                        linear::MatchOp::Eq {
                            path_a: path,
                            path_b,
                        },
                        Some(1),
                    )
                } else {
                    (linear::MatchOp::Nop, None)
                }
            }
            Pattern::Operation(op) => (linear::MatchOp::Opcode { path }, Some(op.operator as u32)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use peepmatic_runtime::{
        integer_interner::IntegerId,
        linear::{Action::*, MatchOp::*},
        operator::Operator,
        r#type::{BitWidth, Kind, Type},
    };

    macro_rules! linearizes_to {
        ($name:ident, $source:expr, $make_expected:expr $(,)* ) => {
            #[test]
            fn $name() {
                let buf = wast::parser::ParseBuffer::new($source).expect("should lex OK");

                let opts = match wast::parser::parse::<Optimizations>(&buf) {
                    Ok(opts) => opts,
                    Err(mut e) => {
                        e.set_path(std::path::Path::new(stringify!($name)));
                        e.set_text($source);
                        eprintln!("{}", e);
                        panic!("should parse OK")
                    }
                };

                assert_eq!(
                    opts.optimizations.len(),
                    1,
                    "`linearizes_to!` only supports a single optimization; split the big test into \
                     multiple small tests"
                );

                if let Err(mut e) = crate::verify(&opts) {
                    e.set_path(std::path::Path::new(stringify!($name)));
                    e.set_text($source);
                    eprintln!("{}", e);
                    panic!("should verify OK")
                }

                let mut paths = PathInterner::new();
                let mut p = |p: &[u8]| paths.intern(Path::new(&p));

                let mut integers = IntegerInterner::new();
                let mut i = |i: u64| integers.intern(i);

                #[allow(unused_variables)]
                let expected = $make_expected(&mut p, &mut i);
                dbg!(&expected);

                let actual = linearize_optimization(&mut paths, &mut integers, &opts.optimizations[0]);
                dbg!(&actual);

                assert_eq!(expected, actual);
            }
        };
    }

    linearizes_to!(
        mul_by_pow2_into_shift,
        "
(=> (when (imul $x $C)
          (is-power-of-two $C))
    (ishl $x $C))
        ",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> IntegerId| {
            linear::Optimization {
                increments: vec![
                    linear::Increment {
                        operation: Opcode { path: p(&[0]) },
                        expected: Some(Operator::Imul as _),
                        actions: vec![
                            GetLhs { path: p(&[0, 0]) },
                            GetLhs { path: p(&[0, 1]) },
                            MakeBinaryInst {
                                operator: Operator::Ishl,
                                r#type: Type {
                                    kind: Kind::Int,
                                    bit_width: BitWidth::Polymorphic,
                                },
                                operands: [linear::RhsId(0), linear::RhsId(1)],
                            },
                        ],
                    },
                    linear::Increment {
                        operation: Nop,
                        expected: None,
                        actions: vec![],
                    },
                    linear::Increment {
                        operation: IsConst { path: p(&[0, 1]) },
                        expected: Some(1),
                        actions: vec![],
                    },
                    linear::Increment {
                        operation: IsPowerOfTwo { path: p(&[0, 1]) },
                        expected: Some(1),
                        actions: vec![],
                    },
                ],
            }
        },
    );

    linearizes_to!(
        variable_pattern_id_optimization,
        "(=> $x $x)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: Nop,
                    expected: None,
                    actions: vec![GetLhs { path: p(&[0]) }],
                }],
            }
        },
    );

    linearizes_to!(
        constant_pattern_id_optimization,
        "(=> $C $C)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: IsConst { path: p(&[0]) },
                    expected: Some(1),
                    actions: vec![GetLhs { path: p(&[0]) }],
                }],
            }
        },
    );

    linearizes_to!(
        boolean_literal_id_optimization,
        "(=> true true)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: BooleanValue { path: p(&[0]) },
                    expected: Some(1),
                    actions: vec![MakeBooleanConst {
                        value: true,
                        bit_width: BitWidth::Polymorphic,
                    }],
                }],
            }
        },
    );

    linearizes_to!(
        number_literal_id_optimization,
        "(=> 5 5)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: IntegerValue { path: p(&[0]) },
                    expected: Some(i(5).into()),
                    actions: vec![MakeIntegerConst {
                        value: i(5),
                        bit_width: BitWidth::Polymorphic,
                    }],
                }],
            }
        },
    );

    linearizes_to!(
        operation_id_optimization,
        "(=> (iconst $C) (iconst $C))",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> IntegerId| {
            linear::Optimization {
                increments: vec![
                    linear::Increment {
                        operation: Opcode { path: p(&[0]) },
                        expected: Some(Operator::Iconst as _),
                        actions: vec![
                            GetLhs { path: p(&[0, 0]) },
                            MakeUnaryInst {
                                operator: Operator::Iconst,
                                r#type: Type {
                                    kind: Kind::Int,
                                    bit_width: BitWidth::Polymorphic,
                                },
                                operand: linear::RhsId(0),
                            },
                        ],
                    },
                    linear::Increment {
                        operation: IsConst { path: p(&[0, 0]) },
                        expected: Some(1),
                        actions: vec![],
                    },
                ],
            }
        },
    );

    linearizes_to!(
        redundant_bor,
        "(=> (bor $x (bor $x $y)) (bor $x $y))",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> IntegerId| {
            linear::Optimization {
                increments: vec![
                    linear::Increment {
                        operation: Opcode { path: p(&[0]) },
                        expected: Some(Operator::Bor as _),
                        actions: vec![
                            GetLhs { path: p(&[0, 0]) },
                            GetLhs {
                                path: p(&[0, 1, 1]),
                            },
                            MakeBinaryInst {
                                operator: Operator::Bor,
                                r#type: Type {
                                    kind: Kind::Int,
                                    bit_width: BitWidth::Polymorphic,
                                },
                                operands: [linear::RhsId(0), linear::RhsId(1)],
                            },
                        ],
                    },
                    linear::Increment {
                        operation: Nop,
                        expected: None,
                        actions: vec![],
                    },
                    linear::Increment {
                        operation: Opcode { path: p(&[0, 1]) },
                        expected: Some(Operator::Bor as _),
                        actions: vec![],
                    },
                    linear::Increment {
                        operation: Eq {
                            path_a: p(&[0, 1, 0]),
                            path_b: p(&[0, 0]),
                        },
                        expected: Some(1),
                        actions: vec![],
                    },
                    linear::Increment {
                        operation: Nop,
                        expected: None,
                        actions: vec![],
                    },
                ],
            }
        },
    );

    linearizes_to!(
        large_integers,
        // u64::MAX
        "(=> 18446744073709551615 0)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: IntegerValue { path: p(&[0]) },
                    expected: Some(i(std::u64::MAX).into()),
                    actions: vec![MakeIntegerConst {
                        value: i(0),
                        bit_width: BitWidth::Polymorphic,
                    }],
                }],
            }
        }
    );

    linearizes_to!(
        ireduce_with_type_ascription,
        "(=> (ireduce{i32} $x) 0)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(u64) -> IntegerId| {
            linear::Optimization {
                increments: vec![
                    linear::Increment {
                        operation: Opcode { path: p(&[0]) },
                        expected: Some(Operator::Ireduce as _),
                        actions: vec![MakeIntegerConst {
                            value: i(0),
                            bit_width: BitWidth::ThirtyTwo,
                        }],
                    },
                    linear::Increment {
                        operation: linear::MatchOp::BitWidth { path: p(&[0]) },
                        expected: Some(32),
                        actions: vec![],
                    },
                    linear::Increment {
                        operation: Nop,
                        expected: None,
                        actions: vec![],
                    },
                ],
            }
        }
    );
}
