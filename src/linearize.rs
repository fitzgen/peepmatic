//! Convert an AST into its linear equivalent.
//!
//! Convert each optimization's left-hand side into a linear series of match
//! operations. This makes it easy to create an automata, because automatas
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
//!   ( Opcode@0,           imul,           [BindLhs(x@0.0), BindLhs(C@0.1), ..] ),
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
//! * We must never have a scope-binding action (i.e. `BindLhs`) until after we
//!   know that the LHS being bound exists. For example, we can't bind the `$x`
//!   or `$C` in `(imul $x $C)` until we've matched an `imul` instruction.
//!
//! * Actions should be pushed as early in the optimization's increment chain as
//!   they can be. This means the tail has fewer side effects, and is therefore
//!   more likely to be share-able with other optimizations in the automata that
//!   we build.
//!
//! * Match operations cannot reference bound LHS variables and constants until
//!   after they've been bound. Similarly, RHS actions cannot reference matches
//!   from the LHS until they've been defined. And finally, an RHS operation's
//!   operands must be defined before the RHS operation itself. In general,
//!   definitions must come before uses! :)
//!
//! * Canonicalize identifier names to enable more state sharing in the
//!   automata.
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
//! As we define the match operations for a pattern, we canonicalize the first
//! identifier we match into `linear::LhsId(0)`, the second identifier as
//! `linear::LhsId(1)`, etc... See `LhsCanonicalizer` for details.
//!
//! The right-hand side is built up incrementally via a post-order traversal,
//! and we only advance this traversal once any bindings from the left-hand side
//! that the traversal's current node depends on are defined. This ensures that
//! an RHS instruction's operands (whether they are from a match in the LHS, or
//! built up in the RHS) are defined before they're used by this RHS
//! instruction. See `RhsPostOrder` and `RhsBuilder`.
//!
//! See `linearize_optimization` for the the main AST optimization into linear
//! optimization translation function.

use crate::ast::*;
use crate::traversals::Dfs;
use peepmatic_runtime::{
    integer_interner::IntegerInterner,
    linear,
    paths::{Path, PathId, PathInterner},
};
use std::collections::BTreeMap;
use std::iter;
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

    // Reusable sink for various `ChildNodes::child_nodes` calls so that we
    // don't make an allocation each time. Clear each time before reusing!
    let mut children = vec![];

    let mut lhs_canonicalizer = LhsCanonicalizer::new();
    let mut rhs_builder = RhsBuilder::new(&opt.rhs);

    // We do a pre-order traversal of the LHS because we don't know whether a
    // child actually exists to match on until we've matched its parent, and we
    // don't want to emit matching operations on things that might not exist!
    let mut patterns = PatternPreOrder::new(&opt.lhs.pattern);
    while let Some((path, pattern)) = patterns.next(paths) {
        // Create the matching parts of an `Increment` for this part of the
        // pattern, without any actions yet.
        let (operation, expected) = pattern.to_linear_match_op(integers, &lhs_canonicalizer, path);
        let mut inc = linear::Increment {
            operation,
            expected,
            actions: vec![],
        };

        // Canonicalize all newly visible LHS bindings in this pattern, building
        // up the actions to add them to scope so they can be used by the RHS.
        lhs_canonicalizer.canonicalize_pattern_ids(
            paths,
            &mut inc.actions,
            &mut children,
            pattern,
            path,
        );

        // Create actions for building up all of the right-hand side that we
        // can right now.
        rhs_builder.add_unblocked_rhs_build_actions(
            integers,
            &lhs_canonicalizer,
            &mut children,
            &mut inc.actions,
        );

        increments.push(inc);
    }

    // Now that we've added all the increments for the LHS pattern, add the
    // increments for its preconditions.
    for pre in &opt.lhs.preconditions {
        increments.push(pre.to_linear_increment(&lhs_canonicalizer));
    }

    // Finally, 99.99% of `Nop` matching operations are unnecessary. Do a quick
    // pass to remove them.
    remove_unnecessary_nops(&mut increments);

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

/// Canonicalizer of matched bindings from a left-hand side.
///
/// Responsible for tracking the identifiers we've already matched on the
/// left-hand side, what their canonical `linear::LhsId` is, and the path within
/// the LHS pattern where we first saw them.
struct LhsCanonicalizer<'a> {
    // A map from `Id::name` to its canonical `linear::LhsId`. In practice, the
    // canonical id is its index in a pre-order traversal of the pattern's
    // identifiers. By canonicalizing identifiers, we should be able to share
    // more states and transitions in the automata.
    canonical_lhs_ids: BTreeMap<&'a str, (linear::LhsId, PathId)>,
}

impl<'a> LhsCanonicalizer<'a> {
    /// Construct a new, empty `LhsCanonicalizer`.
    fn new() -> Self {
        Self {
            canonical_lhs_ids: Default::default(),
        }
    }

    /// Have we already canonicalized the given identifier and brought it into
    /// scope for the RHS?
    fn is_in_scope(&self, id: &Id) -> bool {
        self.canonical_lhs_ids.contains_key(id.name())
    }

    /// Get the canonical `linear::LhsId` for the given AST id.
    ///
    /// ## Panics
    ///
    /// Panics if the given AST id has not already been canonicalized.
    fn get(&self, id: &Id) -> linear::LhsId {
        self.canonical_lhs_ids[id.name()].0
    }

    /// Get the path within the left-hand side pattern where we first saw the
    /// given AST id.
    ///
    /// ## Panics
    ///
    /// Panics if the given AST id has not already been canonicalized.
    fn first_occurrence(&self, id: &Id) -> PathId {
        self.canonical_lhs_ids[id.name()].1
    }

    /// Canonicalize all the newly visible identifiers within the given pattern,
    /// and emit actions to bind them in the LHS scope.
    fn canonicalize_pattern_ids(
        &mut self,
        paths: &mut PathInterner,
        actions: &mut Vec<linear::Action>,
        children: &mut Vec<DynAstRef<'a>>,
        pattern: &'a Pattern<'a>,
        path: PathId,
    ) {
        match pattern {
            // Now that we matched this operation pattern, we know that its
            // children exist, so it is fair game to emit actions to bind them
            // in the LHS scope. We *could* technically wait until we visit them
            // in the pre-order traversal, but peeking ahead here lets us bind
            // them earlier, which lets us build more of the RHS earlier as
            // well.
            Pattern::Operation(op) => {
                let mut child_path = paths.lookup(path).0.to_vec();

                children.clear();
                op.child_nodes(children);

                for (i, child) in children.iter().enumerate() {
                    debug_assert!(i <= (std::u8::MAX as usize));
                    match child {
                        DynAstRef::Pattern(Pattern::Variable(Variable { id, .. }))
                        | DynAstRef::Pattern(Pattern::Constant(Constant { id, .. })) => {
                            child_path.push(i as u8);
                            let child_path_id = paths.intern(Path::new(&child_path));
                            child_path.pop();

                            let (id, is_new) = self.canonicalize_id(id, child_path_id);
                            if is_new {
                                actions.push(linear::Action::BindLhs {
                                    id,
                                    path: child_path_id,
                                });
                            }
                        }
                        _ => {}
                    }
                }
            }

            // If this is the first time we've seen an identifier defined on the
            // left-hand side, create an action to add it to the scope. This
            // will only happen if the whole pattern is a variable or constant,
            // otherwise we would have already canonicalized it after processing
            // its parent `Pattern::Operation`.
            Pattern::Variable(Variable { id, .. }) | Pattern::Constant(Constant { id, .. }) => {
                let (id, is_new) = self.canonicalize_id(id, path);
                if is_new {
                    actions.push(linear::Action::BindLhs { id, path });
                }
            }

            _ => {}
        }
    }

    /// Canonicalize the identifier that is located at the given path.
    ///
    /// Returns a pair of the canonicalized `linear::LhsId` and whether this is
    /// the first time we've seen the id and canonicalized it.
    fn canonicalize_id(&mut self, id: &Id<'a>, path: PathId) -> (linear::LhsId, bool) {
        let new_id = linear::LhsId(self.canonical_lhs_ids.len() as u32);
        let mut is_new = false;
        let (canonical, _) = *self.canonical_lhs_ids.entry(id.name()).or_insert_with(|| {
            is_new = true;
            (new_id, path)
        });
        (canonical, is_new)
    }
}

/// An `RhsBuilder` emits the actions for building the right-hand side
/// instructions.
struct RhsBuilder<'a> {
    // We do a post order traversal of the RHS because an RHS instruction cannot
    // be created until after all of its operands are created.
    rhs_post_order: iter::Peekable<RhsPostOrder<'a>>,

    // A map from a right-hand side's span to its `linear::RhsId`. This is used
    // by RHS-construction actions to reference operands. In practice the
    // `RhsId` is roughly equivalent to its index in the post-order traversal of
    // the RHS.
    rhs_span_to_id: BTreeMap<wast::Span, linear::RhsId>,
}

impl<'a> RhsBuilder<'a> {
    /// Create a new builder for the given right-hand side.
    fn new(rhs: &'a Rhs<'a>) -> Self {
        let rhs_post_order = RhsPostOrder::new(rhs).peekable();
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

    /// Create actions for building up all of the right-hand side that is
    /// currently unblocked.
    ///
    /// A right-hand side instruction is blocked, and cannot be created until
    /// after all of its operands have been created. There are two things we
    /// need to take care of:
    ///
    /// 1. Because we are walking the right-hand side with a post-order
    ///    traversal, we know that we already created an instruction's operands
    ///    that are defined in the right-hand side, before we get to the parent
    ///    instruction.
    ///
    /// 2. However, not all operands are defined in the right-hand side:
    ///    variables and constants matched in the left-hand side might not be
    ///    defined yet.
    ///
    /// Case (2) is what we are primarily concerned with here.
    fn add_unblocked_rhs_build_actions(
        &mut self,
        integers: &mut IntegerInterner,
        lhs_canonicalizer: &LhsCanonicalizer,
        children: &mut Vec<DynAstRef<'a>>,
        actions: &mut Vec<linear::Action>,
    ) {
        while let Some(rhs) = self.rhs_post_order.peek().copied() {
            if self.rhs_is_blocked(lhs_canonicalizer, children, rhs) {
                return;
            }

            actions.push(self.rhs_to_linear_action(integers, lhs_canonicalizer, rhs));
            let id = linear::RhsId(self.rhs_span_to_id.len() as u32);
            self.rhs_span_to_id.insert(rhs.span(), id);

            let _ = self.rhs_post_order.next();
        }
    }

    fn rhs_is_blocked(
        &self,
        lhs_canonicalizer: &LhsCanonicalizer,
        children: &mut Vec<DynAstRef<'a>>,
        rhs: &'a Rhs<'a>,
    ) -> bool {
        children.clear();
        rhs.child_nodes(children);
        children.iter().any(|c| match c {
            DynAstRef::Constant(Constant { id, .. }) | DynAstRef::Variable(Variable { id, .. }) => {
                !lhs_canonicalizer.is_in_scope(id)
            }
            DynAstRef::RhsOperation(_) | DynAstRef::Unquote(_) | DynAstRef::ValueLiteral(_) => {
                false
            }
            ast => unreachable!("impossible AST node: {:?}", ast),
        })
    }

    fn rhs_to_linear_action(
        &self,
        integers: &mut IntegerInterner,
        lhs_canonicalizer: &LhsCanonicalizer,
        rhs: &Rhs,
    ) -> linear::Action {
        match rhs {
            Rhs::ValueLiteral(ValueLiteral::Integer(i)) => linear::Action::MakeIntegerConst {
                value: integers.intern(i.value),
            },
            Rhs::ValueLiteral(ValueLiteral::Boolean(b)) => {
                linear::Action::MakeBooleanConst { value: b.value }
            }
            Rhs::Variable(Variable { id, .. }) | Rhs::Constant(Constant { id, .. }) => {
                linear::Action::GetLhsBinding {
                    id: lhs_canonicalizer.get(id),
                }
            }
            Rhs::Unquote(unq) => match unq.operator {
                UnquoteOperator::Log2 => {
                    let operand = self.get_rhs_id(&unq.operands[0]);
                    linear::Action::Log2 { operand }
                }
            },
            Rhs::Operation(op) => match op.operator {
                Operator::Ashr => linear::Action::MakeAshr {
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                    ],
                },
                Operator::Bor => linear::Action::MakeBor {
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                    ],
                },
                Operator::Iadd => linear::Action::MakeIadd {
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                    ],
                },
                Operator::IaddImm => linear::Action::MakeIaddImm {
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                    ],
                },
                Operator::Iconst => linear::Action::MakeIconst {
                    operand: self.get_rhs_id(&op.operands[0]),
                },
                Operator::Imul => linear::Action::MakeImul {
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                    ],
                },
                Operator::ImulImm => linear::Action::MakeImulImm {
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                    ],
                },
                Operator::Ishl => linear::Action::MakeIshl {
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                    ],
                },
                Operator::Sshr => linear::Action::MakeSshr {
                    operands: [
                        self.get_rhs_id(&op.operands[0]),
                        self.get_rhs_id(&op.operands[1]),
                    ],
                },
            },
        }
    }
}

/// 99.99% of nops are unnecessary. They're only needed for when a LHS pattern
/// is just a variable, and that's it. However, it is easier to have basically
/// unused nop matching operations for the DSL's edge-cases than it is to try
/// and statically eliminate their existence completely. So we just emit nop
/// match operations for all variable patterns, and then in this post-processing
/// pass, we fuse them and their actions with their preceding increment.
fn remove_unnecessary_nops(increments: &mut Vec<linear::Increment>) {
    if increments.len() < 2 {
        debug_assert!(!increments.is_empty());
        return;
    }

    for i in (1..increments.len()).rev() {
        if let linear::MatchOp::Nop = increments[i].operation {
            let nop = increments.remove(i);
            increments[i - 1].actions.extend(nop.actions);
        }
    }
}

impl Precondition<'_> {
    /// Convert this precondition into a `linear::Increment`.
    fn to_linear_increment(&self, lhs_canonicalizer: &LhsCanonicalizer) -> linear::Increment {
        match self.constraint {
            Constraint::IsPowerOfTwo => {
                let id = match &self.operands[0] {
                    ConstraintOperand::Constant(Constant { id, .. }) => id,
                    _ => unreachable!("checked in verification"),
                };
                let id = lhs_canonicalizer.get(&id);
                linear::Increment {
                    operation: linear::MatchOp::IsPowerOfTwo { id },
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
                let id = lhs_canonicalizer.get(&id);

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
                    operation: linear::MatchOp::BitWidth { id },
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
                let id = lhs_canonicalizer.get(&id);
                linear::Increment {
                    operation: linear::MatchOp::FitsInNativeWord { id },
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
        lhs_canonicalizer: &LhsCanonicalizer,
        path: PathId,
    ) -> (linear::MatchOp, Option<u32>) {
        match self {
            Pattern::ValueLiteral(ValueLiteral::Integer(Integer { value, .. })) => (
                linear::MatchOp::IntegerValue { path },
                Some(integers.intern(*value).into()),
            ),
            Pattern::ValueLiteral(ValueLiteral::Boolean(Boolean { value, .. })) => {
                (linear::MatchOp::BooleanValue { path }, Some(*value as u32))
            }
            Pattern::Constant(Constant { id, .. }) => {
                if lhs_canonicalizer.is_in_scope(id)
                    && lhs_canonicalizer.first_occurrence(id) != path
                {
                    let id = lhs_canonicalizer.get(id);
                    (linear::MatchOp::Eq { id, path }, Some(1))
                } else {
                    (linear::MatchOp::IsConst { path }, Some(1))
                }
            }
            Pattern::Variable(Variable { id, .. }) => {
                if lhs_canonicalizer.is_in_scope(id)
                    && lhs_canonicalizer.first_occurrence(id) != path
                {
                    let id = lhs_canonicalizer.get(id);
                    (linear::MatchOp::Eq { id, path }, Some(1))
                } else {
                    (linear::MatchOp::Nop, None)
                }
            }
            Pattern::Operation(op) => (
                linear::MatchOp::Opcode { path },
                // TODO: Ideally, this would match the value of
                // `cranelift_codegen::ir::instructions::Opcode` (assuming that
                // becomes a C-style `enum`). This would allow the matcher to
                // avoid an extra switch-and-translate, and instead use the
                // opcode as the lookup key for the transition directly.
                Some(match op.operator {
                    Operator::Ashr => 0,
                    Operator::Bor => 1,
                    Operator::Iadd => 2,
                    Operator::IaddImm => 3,
                    Operator::Iconst => 4,
                    Operator::Imul => 5,
                    Operator::ImulImm => 6,
                    Operator::Ishl => 7,
                    Operator::Sshr => 8,
                }),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use peepmatic_runtime::integer_interner::IntegerId;

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
                let mut i = |i: i128| integers.intern(i);

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
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(i128) -> IntegerId| {
            linear::Optimization {
                increments: vec![
                    linear::Increment {
                        operation: linear::MatchOp::Opcode { path: p(&[0]) },
                        expected: Some(5),
                        actions: vec![
                            linear::Action::BindLhs {
                                id: linear::LhsId(0),
                                path: p(&[0, 0]),
                            },
                            linear::Action::BindLhs {
                                id: linear::LhsId(1),
                                path: p(&[0, 1]),
                            },
                            linear::Action::GetLhsBinding {
                                id: linear::LhsId(0),
                            },
                            linear::Action::GetLhsBinding {
                                id: linear::LhsId(1),
                            },
                            linear::Action::MakeIshl {
                                operands: [linear::RhsId(0), linear::RhsId(1)],
                            },
                        ],
                    },
                    linear::Increment {
                        operation: linear::MatchOp::IsConst { path: p(&[0, 1]) },
                        expected: Some(1),
                        actions: vec![],
                    },
                    linear::Increment {
                        operation: linear::MatchOp::IsPowerOfTwo {
                            id: linear::LhsId(1),
                        },
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
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(i128) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: linear::MatchOp::Nop,
                    expected: None,
                    actions: vec![
                        linear::Action::BindLhs {
                            id: linear::LhsId(0),
                            path: p(&[0]),
                        },
                        linear::Action::GetLhsBinding {
                            id: linear::LhsId(0),
                        },
                    ],
                }],
            }
        },
    );

    linearizes_to!(
        constant_pattern_id_optimization,
        "(=> $C $C)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(i128) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: linear::MatchOp::IsConst { path: p(&[0]) },
                    expected: Some(1),
                    actions: vec![
                        linear::Action::BindLhs {
                            id: linear::LhsId(0),
                            path: p(&[0]),
                        },
                        linear::Action::GetLhsBinding {
                            id: linear::LhsId(0),
                        },
                    ],
                }],
            }
        },
    );

    linearizes_to!(
        boolean_literal_id_optimization,
        "(=> true true)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(i128) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: linear::MatchOp::BooleanValue { path: p(&[0]) },
                    expected: Some(1),
                    actions: vec![linear::Action::MakeBooleanConst { value: true }],
                }],
            }
        },
    );

    linearizes_to!(
        number_literal_id_optimization,
        "(=> 5 5)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(i128) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: linear::MatchOp::IntegerValue { path: p(&[0]) },
                    expected: Some(i(5).into()),
                    actions: vec![linear::Action::MakeIntegerConst { value: i(5) }],
                }],
            }
        },
    );

    linearizes_to!(
        operation_id_optimization,
        "(=> (iconst $C) (iconst $C))",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(i128) -> IntegerId| {
            linear::Optimization {
                increments: vec![
                    linear::Increment {
                        operation: linear::MatchOp::Opcode { path: p(&[0]) },
                        expected: Some(4),
                        actions: vec![
                            linear::Action::BindLhs {
                                id: linear::LhsId(0),
                                path: p(&[0, 0]),
                            },
                            linear::Action::GetLhsBinding {
                                id: linear::LhsId(0),
                            },
                            linear::Action::MakeIconst {
                                operand: linear::RhsId(0),
                            },
                        ],
                    },
                    linear::Increment {
                        operation: linear::MatchOp::IsConst { path: p(&[0, 0]) },
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
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(i128) -> IntegerId| {
            linear::Optimization {
                increments: vec![
                    linear::Increment {
                        operation: linear::MatchOp::Opcode { path: p(&[0]) },
                        expected: Some(1),
                        actions: vec![
                            linear::Action::BindLhs {
                                id: linear::LhsId(0),
                                path: p(&[0, 0]),
                            },
                            linear::Action::GetLhsBinding {
                                id: linear::LhsId(0),
                            },
                        ],
                    },
                    linear::Increment {
                        operation: linear::MatchOp::Opcode { path: p(&[0, 1]) },
                        expected: Some(1),
                        actions: vec![
                            linear::Action::BindLhs {
                                id: linear::LhsId(1),
                                path: p(&[0, 1, 1]),
                            },
                            linear::Action::GetLhsBinding {
                                id: linear::LhsId(1),
                            },
                            linear::Action::MakeBor {
                                operands: [linear::RhsId(0), linear::RhsId(1)],
                            },
                        ],
                    },
                    linear::Increment {
                        operation: linear::MatchOp::Eq {
                            id: linear::LhsId(0),
                            path: p(&[0, 1, 0]),
                        },
                        expected: Some(1),
                        actions: vec![],
                    },
                ],
            }
        },
    );

    linearizes_to!(
        large_integers,
        // i128::MAX
        "(=> 170141183460469231731687303715884105727 0)",
        |p: &mut dyn FnMut(&[u8]) -> PathId, i: &mut dyn FnMut(i128) -> IntegerId| {
            linear::Optimization {
                increments: vec![linear::Increment {
                    operation: linear::MatchOp::IntegerValue { path: p(&[0]) },
                    expected: Some(i(170141183460469231731687303715884105727).into()),
                    actions: vec![linear::Action::MakeIntegerConst { value: i(0) }],
                }],
            }
        }
    );
}
