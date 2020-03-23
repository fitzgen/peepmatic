use peepmatic_macro::{peepmatic, Span};
use wast::Id;

/// A trait for getting the span where an AST node was defined.
///
/// This is mostly implemented automatically with `derive(Span)` -- see
/// `derive_span` in `crates/macro/src/lib.rs`.
pub(crate) trait Span {
    fn span(&self) -> wast::Span;
}

/// A set of optimizations.
///
/// This is the root AST node.
#[derive(Debug)]
pub struct Optimizations<'a>(pub Vec<Optimization<'a>>);

/// A complete optimization: a left-hand side to match against and a right-hand
/// side replacement.
#[derive(Debug, Span)]
pub struct Optimization<'a> {
    /// Where this `Optimization` was defined.
    pub span: wast::Span,

    /// The left-hand side that matches when this optimization applies.
    pub lhs: Lhs<'a>,

    /// The new sequence of instructions to replace an old sequence that matches
    /// the left-hand side with.
    pub rhs: Rhs<'a>,
}

/// A left-hand side describes what is required for a particular optimization to
/// apply.
///
/// A left-hand side has two parts: a structural pattern for describing
/// candidate instruction sequences, and zero or more preconditions that add
/// additional constraints upon instruction sequences matched by the pattern.
#[derive(Debug, Span)]
pub struct Lhs<'a> {
    /// Where this `Lhs` was defined.
    pub span: wast::Span,

    /// A pattern that describes sequences of instructions to match.
    pub pattern: Pattern<'a>,

    /// Additional constraints that a match must satisfy in addition to
    /// structually matching the pattern, e.g. some constant must be a power of
    /// two.
    pub preconditions: Vec<Precondition<'a>>,
}

/// A structural pattern, potentially with wildcard variables for matching whole
/// subtrees.
#[derive(Debug, Span)]
pub enum Pattern<'a> {
    /// A specific value. These are written as `1234` or `0x1234` or `true` or
    /// `false`.
    ValueLiteral(ValueLiteral),

    /// A constant that matches any constant value. This subsumes value
    /// patterns. These are upper-case identifiers like `$C`.
    Constant(Constant<'a>),

    /// An operation pattern with zero or more operand patterns. These are
    /// s-expressions like `(iadd $x $y)`.
    Operation(Operation<Pattern<'a>>),

    /// A variable that matches any kind of subexpression. This subsumes all
    /// other patterns. These are lower-case identifiers like `$x`.
    Variable(Variable<'a>),
}

/// An integer or boolean value literal.
#[derive(Debug, Span)]
pub enum ValueLiteral {
    /// An integer value.
    Integer(Integer),

    /// A boolean value: `true` or `false`.
    Boolean(Boolean),
}

/// An integer literal.
#[derive(Debug, Span)]
pub struct Integer {
    /// Where this `Integer` was defined.
    pub span: wast::Span,

    /// The integer value.
    pub value: i128,
}

/// A boolean literal.
#[derive(Debug, Span)]
pub struct Boolean {
    /// Where this `Boolean` was defined.
    pub span: wast::Span,

    /// The boolean value.
    pub value: bool,
}

/// A symbolic constant.
///
/// These are identifiers containing uppercase letters: `$C`, `$MY-CONST`,
/// `$CONSTANT1`.
#[derive(Debug, Span)]
pub struct Constant<'a> {
    /// Where this `Constant` was defined.
    pub span: wast::Span,

    /// This constant's identifier.
    pub id: Id<'a>,
}

/// A variable that matches any subtree.
///
/// Duplicate uses of the same variable constrain each occurrence's match to
/// being the same as each other occurrence as well, e.g. `(iadd $x $x)` matches
/// `(iadd 5 5)` but not `(iadd 1 2)`.
#[derive(Debug, Span)]
pub struct Variable<'a> {
    /// Where this `Variable` was defined.
    pub span: wast::Span,

    /// This variable's identifier.
    pub id: Id<'a>,
}

/// An operation with an operator, and operands of type `T`.
#[derive(Debug, Span)]
pub struct Operation<T> {
    /// The span where this operation was written.
    pub span: wast::Span,

    /// The operator for this operation, e.g. `imul` or `iadd`.
    pub operator: Operator,

    /// This operation's operands.
    ///
    /// When `Operation` is used in a pattern, these are the sub-patterns for
    /// the operands. When `Operation is used in a right-hand side replacement,
    /// these are the sub-replacements for the operands.
    pub operands: Vec<T>,
}

/// An operator.
///
/// These are a subset of Cranelift IR's operators.
#[peepmatic]
#[derive(Debug)]
pub enum Operator {
    /// `ashr`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Ashr,

    /// `bor`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Bor,

    /// `iadd`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Iadd,

    /// `iadd_imm`
    #[peepmatic(immediates(iNN), params(iNN), result(iNN))]
    IaddImm,

    /// `iconst`
    #[peepmatic(immediates(iNN), result(iNN))]
    Iconst,

    /// `imul`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Imul,

    /// `ishl`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Ishl,

    /// `sshr`
    #[peepmatic(params(iNN, iNN), result(iNN))]
    Sshr,
}

/// A precondition adds additional constraints to a pattern, such as "$C must be
/// a power of two".
#[derive(Debug, Span)]
pub struct Precondition<'a> {
    /// Where this `Precondition` was defined.
    pub span: wast::Span,

    /// The constraint operator.
    pub constraint: Constraint,

    /// The operands of the constraint.
    pub operands: Vec<ConstraintOperand<'a>>,
}

/// Contraint operators.
#[derive(Debug)]
pub enum Constraint {
    /// Is the operand a power of two?
    IsPowerOfTwo,

    /// Check the bit width of a value.
    BitWidth,
}

/// An operand of a precondition's constraint.
#[derive(Debug, Span)]
pub enum ConstraintOperand<'a> {
    /// A value literal operand.
    ValueLiteral(ValueLiteral),

    /// A constant operand.
    Constant(Constant<'a>),

    /// A variable operand.
    Variable(Variable<'a>),
}

/// The right-hand side of an optimization that contains the instructions to
/// replace any matched left-hand side with.
#[derive(Debug, Span)]
pub enum Rhs<'a> {
    /// A value literal right-hand side.
    ValueLiteral(ValueLiteral),

    /// A constant right-hand side (the constant must have been matched and
    /// bound in the left-hand side's pattern).
    Constant(Constant<'a>),

    /// A variable right-hand side (the variable must have been matched and
    /// bound in the left-hand side's pattern).
    Variable(Variable<'a>),

    /// An unquote expression that is evaluated while replacing the left-hand
    /// side with the right-hand side. The result of the evaluation is used in
    /// the replacement.
    Unquote(Unquote<'a>),

    /// A compound right-hand side consisting of an operation and subsequent
    /// right-hand side operands.
    Operation(Operation<Rhs<'a>>),
}

/// An unquote operation.
///
/// Rather than replaciong a left-hand side, these are evaluated and then the
/// result of the evaluation replaces the left-hand side. This allows for
/// compile-time computation while replacing a matched left-hand side with a
/// right-hand side.
///
/// For example, given the unqouted right-hand side `$(log2 $C)`, we replace any
/// instructions that match its left-hand side with the compile-time result of
/// `log2($C)` (the left-hand side must match and bind the constant `$C`).
#[derive(Debug, Span)]
pub struct Unquote<'a> {
    /// Where this `Unquote` was defined.
    pub span: wast::Span,

    /// The operator for this unquote operation.
    pub operator: UnquoteOperator,

    /// The operands for this unquote operation.
    pub operands: Vec<UnquoteOperand<'a>>,
}

/// Valid operators for compile-time unquote operations.
#[derive(Debug)]
pub enum UnquoteOperator {
    /// Take the base-2 log of a power of two integer.
    Log2,
}

/// An operand for an unquote operation.
#[derive(Debug, Span)]
pub enum UnquoteOperand<'a> {
    /// A value-literal operand.
    ValueLiteral(ValueLiteral),

    /// A constant operand. The constant must have been defined and matched in
    /// the left-hand side pattern.
    Constant(Constant<'a>),
}
