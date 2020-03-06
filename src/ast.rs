use wast::{Id, Span};

/// A set of optimizations.
///
/// This is the top-level production, and root AST node.
///
/// ```text
/// <optimizations> ::= <optimization>*
/// ```
#[derive(Debug)]
pub struct Optimizations<'a>(pub Vec<Optimization<'a>>);

/// A complete optimization: a left-hand side to match against and a right-hand
/// side replacement.
///
/// ```text
/// <optimization> ::= '(' '=>' <lhs> <rhs> ')'
/// ```
#[derive(Debug)]
pub struct Optimization<'a> {
    /// Where this `Optimization` was defined.
    pub span: Span,

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
///
/// ```text
/// <left-hand-side> ::= <pattern>
///                    | '(' 'when' <pattern> <precondition>* ')'
/// ```
#[derive(Debug)]
pub struct Lhs<'a> {
    /// A pattern that describes sequences of instructions to match.
    pub pattern: Pattern<'a>,

    /// Additional constraints that a match must satisfy in addition to
    /// structually matching the pattern, e.g. some constant must be a power of
    /// two.
    pub preconditions: Vec<Precondition<'a>>,
}

/// A structural pattern, potentially with wildcard variables for matching whole
/// subtrees.
///
/// ```text
/// <pattern> ::= <value-literal>
///             | <constant>
///             | <operation-pattern>
///             | <variable>
/// ```
#[derive(Debug)]
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
///
/// ```text
/// <value> ::= <integer>
///           | <boolean>
/// ```
#[derive(Debug)]
pub enum ValueLiteral {
    /// An integer value.
    Integer(Integer),

    /// A boolean value: `true` or `false`.
    Boolean(Boolean),
}

/// An integer literal.
#[derive(Debug)]
pub struct Integer(pub i128);

/// A boolean literal.
///
/// ```text
/// <boolean> ::= 'true' | 'false'
/// ```
#[derive(Debug)]
pub enum Boolean {
    /// The `true` value.
    True,

    /// The `false` value.
    False,
}

/// A symbolic constant.
///
/// These are identifiers that start with an upper-case letter: `$C`.
#[derive(Debug)]
pub struct Constant<'a>(pub Id<'a>);

/// A variable that matches any subtree.
///
/// Duplicate uses of the same variable constrain each occurrence's match to
/// being the same as each other occurrence as well, e.g. `(iadd $x $x)` matches
/// `(iadd 5 5)` but not `(iadd 1 2)`.
#[derive(Debug)]
pub struct Variable<'a>(pub Id<'a>);

/// An operation with an operator, and operands of type `T`.
///
/// ```text
/// operation<T> ::= '(' <operator> <T>* ')'
/// ```
#[derive(Debug)]
pub struct Operation<T> {
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
#[derive(Debug)]
pub enum Operator {
    /// `ashr`
    Ashr,

    /// `iadd`
    Iadd,

    /// `iadd_imm`
    IaddImm,

    /// `iconst`
    Iconst,

    /// `imul`
    Imul,

    /// `ishl`
    Ishl,

    /// `sshr`
    Sshr,
}

/// A precondition adds additional constraints to a pattern, such as "$C must be
/// a power of two".
///
/// ```text
/// <precondition> ::= '(' <constraint> <constraint-operands>* ')'
/// ```
#[derive(Debug)]
pub struct Precondition<'a> {
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
}

/// An operand of a precondition's constraint.
///
/// ```text
/// <constraint-operand> ::= <value-literal>
///                        | <constant>
///                        | <variable>
/// ```
#[derive(Debug)]
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
///
/// ```text
/// <rhs> ::= <value-literal>
///         | <constant>
///         | <variable>
///         | <unquote>
///         | <operation<rhs>>
/// ```
#[derive(Debug)]
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
///
/// ```text
/// <unquote> ::= '$' '(' <unquote-operator> <unquote-operand>* ')'
/// ```
#[derive(Debug)]
pub struct Unquote<'a> {
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
///
/// ```text
/// <unquote-operand> ::= <value-literal>
///                     | <constant>
/// ```
#[derive(Debug)]
pub enum UnquoteOperand<'a> {
    /// A value-literal operand.
    ValueLiteral(ValueLiteral),

    /// A constant operand. The constant must have been defined and matched in
    /// the left-hand side pattern.
    Constant(Constant<'a>),
}
