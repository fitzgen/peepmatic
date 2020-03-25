//! Verification and type checking of optimizations.
//!
//! For type checking, we compile the AST's type constraints down into Z3
//! variables and assertions. If Z3 finds the assertions satisfiable, then we're
//! done! If it finds them unsatisfiable, we use the `get_unsat_core` method to
//! get the minimal subset of assertions that are in conflict, and report a
//! best-effort type error message with them. These messages aren't perfect, but
//! they're Good Enough when embedded in the source text via our tracking of
//! `wast::Span`s.
//!
//! Verifying that there aren't any counter-examples (inputs for which the LHS
//! and RHS produce different results) for a particular optimization is not
//! implemented yet.

use crate::ast::{Span as _, *};
use crate::traversals::Dfs;
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;
use std::ops::{Deref, DerefMut};
use std::path::Path;
use wast::{Error as WastError, Id, Span};
use z3::ast::Ast;

/// A verification or type checking error.
#[derive(Debug)]
pub struct VerifyError {
    errors: Vec<anyhow::Error>,
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for e in &self.errors {
            writeln!(f, "{}\n", e)?;
        }
        Ok(())
    }
}

impl std::error::Error for VerifyError {}

impl From<WastError> for VerifyError {
    fn from(e: WastError) -> Self {
        VerifyError {
            errors: vec![e.into()],
        }
    }
}

impl From<anyhow::Error> for VerifyError {
    fn from(e: anyhow::Error) -> Self {
        VerifyError { errors: vec![e] }
    }
}

impl VerifyError {
    /// To provide a more useful error this function can be used to extract
    /// relevant textual information about this error into the error itself.
    ///
    /// The `contents` here should be the full text of the original file being
    /// parsed, and this will extract a sub-slice as necessary to render in the
    /// `Display` implementation later on.
    pub fn set_text(&mut self, contents: &str) {
        for e in &mut self.errors {
            if let Some(e) = e.downcast_mut::<WastError>() {
                e.set_text(contents);
            }
        }
    }

    /// To provide a more useful error this function can be used to set
    /// the file name that this error is associated with.
    ///
    /// The `path` here will be stored in this error and later rendered in the
    /// `Display` implementation.
    pub fn set_path(&mut self, path: &Path) {
        for e in &mut self.errors {
            if let Some(e) = e.downcast_mut::<WastError>() {
                e.set_path(path);
            }
        }
    }
}

/// Either `Ok(T)` or `Err(VerifyError)`.
pub type VerifyResult<T> = Result<T, VerifyError>;

/// Verify and type check a set of optimizations.
pub fn verify(opts: &Optimizations) -> VerifyResult<()> {
    let z3 = &z3::Context::new(&z3::Config::new());
    for opt in opts.optimizations.iter() {
        verify_optimization(z3, opt)?;
    }
    Ok(())
}

pub(crate) struct TypingContext<'a> {
    z3: &'a z3::Context,
    type_kind_sort: z3::DatatypeSort<'a>,
    type_width_sort: z3::DatatypeSort<'a>,

    // See the comments above `enter_operation_scope`.
    operation_scope: HashMap<&'static str, TypeVar<'a>>,

    // A map from identifiers to the type variable describing its type.
    id_to_type_var: HashMap<Id<'a>, TypeVar<'a>>,

    // A list of type constraints, the span of the AST node where the constraint
    // originates from, and an optional message to be displayed if the
    // constraint is not satisfied.
    constraints: Vec<(z3::ast::Bool<'a>, Span, Option<Cow<'static, str>>)>,
}

impl<'a> TypingContext<'a> {
    fn new(z3: &'a z3::Context) -> Self {
        let type_kind_sort = z3::DatatypeBuilder::new(z3)
            .variant("int", &[])
            .variant("bool", &[])
            .finish("TypeKind");
        let type_width_sort = z3::DatatypeBuilder::new(z3)
            .variant("1", &[])
            .variant("8", &[])
            .variant("16", &[])
            .variant("32", &[])
            .variant("64", &[])
            .variant("128", &[])
            .finish("TypeWidth");
        TypingContext {
            z3,
            operation_scope: Default::default(),
            id_to_type_var: Default::default(),
            type_kind_sort,
            type_width_sort,
            constraints: vec![],
        }
    }

    fn new_type_var(&self) -> TypeVar<'a> {
        let kind =
            z3::ast::Datatype::fresh_const(self.z3, "type-var-kind", &self.type_kind_sort.sort);
        let width =
            z3::ast::Datatype::fresh_const(self.z3, "type-var-width", &self.type_width_sort.sort);
        TypeVar { kind, width }
    }

    fn get_or_create_type_var_for_id(&mut self, id: Id<'a>) -> TypeVar<'a> {
        if let Some(ty) = self.id_to_type_var.get(&id) {
            ty.clone()
        } else {
            // Note: can't use the entry API because we reborrow `self` here.
            let ty = self.new_type_var();
            self.id_to_type_var.insert(id, ty.clone());
            ty
        }
    }

    fn get_type_var_for_id(&mut self, id: Id<'a>) -> VerifyResult<TypeVar<'a>> {
        if let Some(ty) = self.id_to_type_var.get(&id) {
            Ok(ty.clone())
        } else {
            Err(WastError::new(id.span(), format!("unknown identifier: ${}", id.name())).into())
        }
    }

    // The `#[peepmatic]` macro for operations allows defining operations' types
    // like `(iNN, iNN) -> iNN` where `iNN` all refer to the same integer type
    // variable that must have the same bit width. But other operations might
    // *also* have that type signature but be instantiated at a different bit
    // width. We don't want to mix up which `iNN` variables are and aren't the
    // same. We use this method to track scopes within which all uses of `iNN`
    // and similar refer to the same type variables.
    fn enter_operation_scope<'b>(
        &'b mut self,
    ) -> impl DerefMut<Target = TypingContext<'a>> + Drop + 'b {
        assert!(self.operation_scope.is_empty());
        return Scope(self);

        struct Scope<'a, 'b>(&'b mut TypingContext<'a>)
        where
            'a: 'b;

        impl<'a, 'b> Deref for Scope<'a, 'b>
        where
            'a: 'b,
        {
            type Target = TypingContext<'a>;
            fn deref(&self) -> &TypingContext<'a> {
                self.0
            }
        }

        impl<'a, 'b> DerefMut for Scope<'a, 'b>
        where
            'a: 'b,
        {
            fn deref_mut(&mut self) -> &mut TypingContext<'a> {
                self.0
            }
        }

        impl Drop for Scope<'_, '_> {
            fn drop(&mut self) {
                self.0.operation_scope.clear();
            }
        }
    }

    #[allow(non_snake_case)]
    pub(crate) fn iNN(&mut self, span: Span) -> TypeVar<'a> {
        if let Some(ty) = self.operation_scope.get("iNN") {
            return ty.clone();
        }

        let ty = self.new_type_var();
        self.assert_is_integer(span, &ty);
        self.operation_scope.insert("iNN", ty.clone());
        ty
    }

    fn assert_is_integer(&mut self, span: Span, ty: &TypeVar<'a>) {
        let is_int = self.type_kind_sort.variants[0]
            .tester
            .apply(&[&ty.kind.clone().into()])
            .as_bool()
            .unwrap();
        self.constraints
            .push((is_int, span, Some("type error: expected integer".into())));
    }

    fn assert_is_bool(&mut self, span: Span, ty: &TypeVar<'a>) {
        let is_bool = self.type_kind_sort.variants[1]
            .tester
            .apply(&[&ty.kind.clone().into()])
            .as_bool()
            .unwrap();
        self.constraints
            .push((is_bool, span, Some("type error: expected bool".into())));
    }

    fn assert_bit_width(&mut self, span: Span, ty: &TypeVar<'a>, width: u8) {
        let width_var = self.type_width_sort.variants[match width {
            1 => 0,
            8 => 1,
            16 => 2,
            32 => 3,
            64 => 4,
            128 => 5,
            w => panic!("unsupported bit width: {}", w),
        }]
        .constructor
        .apply(&[])
        .as_datatype()
        .unwrap();
        let is_width = width_var._eq(&ty.width);
        self.constraints.push((
            is_width,
            span,
            Some(format!("type error: expected bit width = {}", width).into()),
        ));
    }

    fn assert_type_eq(
        &mut self,
        span: Span,
        lhs: &TypeVar<'a>,
        rhs: &TypeVar<'a>,
        msg: Option<Cow<'static, str>>,
    ) {
        self.constraints
            .push((lhs.kind._eq(&rhs.kind), span, msg.clone()));
        self.constraints
            .push((lhs.width._eq(&rhs.width), span, msg));
    }

    fn type_check(&self, span: Span) -> VerifyResult<()> {
        let solver = z3::Solver::new(self.z3);

        let trackers =
            std::iter::repeat_with(|| z3::ast::Bool::fresh_const(self.z3, "type-constraint"))
                .take(self.constraints.len())
                .collect::<Vec<_>>();

        let mut tracker_to_diagnostics = HashMap::with_capacity(self.constraints.len());

        for (constraint_data, tracker) in self.constraints.iter().zip(trackers) {
            let (constraint, span, msg) = constraint_data;
            solver.assert_and_track(constraint, &tracker);
            tracker_to_diagnostics.insert(tracker, (*span, msg.clone()));
        }

        match solver.check() {
            z3::SatResult::Sat => Ok(()),
            z3::SatResult::Unsat => {
                let core = solver.get_unsat_core();
                if core.is_empty() {
                    return Err(WastError::new(
                        span,
                        "z3 determined the type constraints for this optimization are \
                         unsatisfiable, meaning there is a type error, but z3 did not give us any \
                         additional information"
                            .into(),
                    )
                    .into());
                }

                let mut errors = core
                    .iter()
                    .map(|tracker| {
                        let (span, msg) = &tracker_to_diagnostics[tracker];
                        (
                            *span,
                            WastError::new(
                                *span,
                                msg.clone().unwrap_or("type error".into()).into(),
                            )
                            .into(),
                        )
                    })
                    .collect::<Vec<_>>();
                errors.sort_by_key(|(span, _)| *span);
                let errors = errors.into_iter().map(|(_, e)| e).collect();

                Err(VerifyError { errors })
            }
            z3::SatResult::Unknown => Err(anyhow::anyhow!(
                "z3 returned 'unknown' when evaluating type constraints: {}",
                solver
                    .get_reason_unknown()
                    .unwrap_or_else(|| "<no reason given>".into())
            )
            .into()),
        }
    }
}

#[derive(Clone)]
pub(crate) struct TypeVar<'a> {
    kind: z3::ast::Datatype<'a>,
    width: z3::ast::Datatype<'a>,
}

fn verify_optimization(z3: &z3::Context, opt: &Optimization) -> VerifyResult<()> {
    let mut context = TypingContext::new(z3);
    collect_type_constraints(&mut context, &opt)?;
    context.type_check(opt.span)?;

    // TODO: add another pass here to check for counter-examples to this
    // optimization, i.e. inputs where the LHS and RHS are not equivalent.

    Ok(())
}

fn collect_type_constraints<'a>(
    context: &mut TypingContext<'a>,
    opt: &'a Optimization<'a>,
) -> VerifyResult<()> {
    use crate::traversals::TraversalEvent as TE;

    let lhs_ty = context.new_type_var();
    let rhs_ty = context.new_type_var();
    context.assert_type_eq(
        opt.span,
        &lhs_ty,
        &rhs_ty,
        Some("type error: the left-hand side and right-hand side must have the same type".into()),
    );

    // A stack of type variables that we are constraining as we traverse the
    // AST. Operations push new type variables for their operands' expected
    // types, and exiting a `Pattern` in the traversal pops them off.
    let mut expected_types = vec![lhs_ty];

    // Build up the type constraints for the left-hand side.
    for (event, node) in Dfs::new(&opt.lhs) {
        match (event, node) {
            (TE::Enter, DynAstRef::Pattern(Pattern::Constant(Constant { id, span })))
            | (TE::Enter, DynAstRef::Pattern(Pattern::Variable(Variable { id, span }))) => {
                let id = context.get_or_create_type_var_for_id(*id);
                context.assert_type_eq(*span, expected_types.last().unwrap(), &id, None);
            }
            (
                TE::Enter,
                DynAstRef::Pattern(Pattern::ValueLiteral(ValueLiteral::Integer(Integer {
                    span,
                    ..
                }))),
            ) => {
                context.assert_is_integer(*span, expected_types.last().unwrap());
            }
            (
                TE::Enter,
                DynAstRef::Pattern(Pattern::ValueLiteral(ValueLiteral::Boolean(Boolean {
                    span,
                    ..
                }))),
            ) => {
                context.assert_is_bool(*span, expected_types.last().unwrap());
            }
            (TE::Enter, DynAstRef::PatternOperation(op)) => {
                let result_ty;
                let mut operand_types = vec![];
                {
                    let mut scope = context.enter_operation_scope();
                    result_ty = op.operator.result_type(&mut scope, op.span);
                    op.operator
                        .immediate_types(&mut scope, op.span, &mut operand_types);
                    op.operator
                        .param_types(&mut scope, op.span, &mut operand_types);
                }

                if op.operands.len() != operand_types.len() {
                    return Err(WastError::new(
                        op.span,
                        format!(
                            "Expected {} operands but found {}",
                            operand_types.len(),
                            op.operands.len()
                        ),
                    )
                    .into());
                }

                context.assert_type_eq(op.span, expected_types.last().unwrap(), &result_ty, None);

                operand_types.reverse();
                expected_types.extend(operand_types);
            }
            (TE::Exit, DynAstRef::Pattern(..)) => {
                expected_types.pop().unwrap();
            }
            (TE::Enter, DynAstRef::Precondition(pre)) => {
                type_constrain_precondition(context, pre)?;
            }
            _ => continue,
        }
    }

    // We should have exited exactly as many patterns as we entered: one for the
    // root pattern and the initial `lhs_ty`, and then the rest for the operands
    // of pattern operations.
    assert!(expected_types.is_empty());

    // Collect the type constraints for the right-hand side.
    expected_types.push(rhs_ty);
    for (event, node) in Dfs::new(&opt.rhs) {
        match (event, node) {
            (
                TE::Enter,
                DynAstRef::Rhs(Rhs::ValueLiteral(ValueLiteral::Integer(Integer { span, .. }))),
            ) => {
                context.assert_is_integer(*span, expected_types.last().unwrap());
            }
            (
                TE::Enter,
                DynAstRef::Rhs(Rhs::ValueLiteral(ValueLiteral::Boolean(Boolean { span, .. }))),
            ) => {
                context.assert_is_bool(*span, expected_types.last().unwrap());
            }
            (TE::Enter, DynAstRef::Rhs(Rhs::Constant(Constant { span, id })))
            | (TE::Enter, DynAstRef::Rhs(Rhs::Variable(Variable { span, id }))) => {
                let id_ty = context.get_type_var_for_id(*id)?;
                context.assert_type_eq(*span, expected_types.last().unwrap(), &id_ty, None);
            }
            (TE::Enter, DynAstRef::RhsOperation(op)) => {
                let result_ty;
                let mut operand_types = vec![];
                {
                    let mut scope = context.enter_operation_scope();
                    result_ty = op.operator.result_type(&mut scope, op.span);
                    op.operator
                        .immediate_types(&mut scope, op.span, &mut operand_types);
                    op.operator
                        .param_types(&mut scope, op.span, &mut operand_types);
                }

                if op.operands.len() != operand_types.len() {
                    return Err(WastError::new(
                        op.span,
                        format!(
                            "Expected {} operands but found {}",
                            operand_types.len(),
                            op.operands.len()
                        ),
                    )
                    .into());
                }

                context.assert_type_eq(op.span, expected_types.last().unwrap(), &result_ty, None);

                operand_types.reverse();
                expected_types.extend(operand_types);
            }
            (TE::Enter, DynAstRef::Unquote(unq)) => match unq.operator {
                UnquoteOperator::Log2 => {
                    if unq.operands.len() != 1 {
                        return Err(WastError::new(
                                unq.span,
                                format!(
                                    "the `log2` unquote operatore requires exactly 1 operand, found {} \
                                     operands",
                                    unq.operands.len()
                                ),
                            )
                                   .into());
                    }
                    context.assert_is_integer(unq.span, expected_types.last().unwrap());
                }
            },
            (TE::Exit, DynAstRef::Rhs(..)) => {
                expected_types.pop().unwrap();
            }
            _ => continue,
        }
    }

    // Again, we should have popped off all the expected types when exiting
    // `Rhs` nodes in the traversal.
    assert!(expected_types.is_empty());

    Ok(())
}

fn type_constrain_precondition<'a>(
    context: &mut TypingContext<'a>,
    pre: &Precondition<'a>,
) -> VerifyResult<()> {
    match pre.constraint {
        Constraint::BitWidth => {
            if pre.operands.len() != 2 {
                return Err(WastError::new(
                    pre.span,
                    format!(
                        "the `bit-width` precondition requires exactly 2 operands, found \
                         {} operands",
                        pre.operands.len(),
                    ),
                )
                .into());
            }

            let id = match pre.operands[0] {
                ConstraintOperand::ValueLiteral(_) => {
                    return Err(anyhow::anyhow!(
                        "the `bit-width` precondition requires a constant or variable as \
                     its first operand"
                    )
                    .into())
                }
                ConstraintOperand::Constant(Constant { id, .. })
                | ConstraintOperand::Variable(Variable { id, .. }) => id,
            };

            let width = match pre.operands[1] {
                ConstraintOperand::ValueLiteral(ValueLiteral::Integer(Integer {
                    value, ..
                })) if value == 1
                    || value == 8
                    || value == 16
                    || value == 32
                    || value == 64
                    || value == 128 =>
                {
                    value as u8
                }
                ref op => return Err(WastError::new(
                    op.span(),
                    "the `bit-width` precondition requires a bit width of 1, 8, 16, 32, 64, or \
                     128"
                    .into(),
                )
                .into()),
            };

            let ty = context.get_type_var_for_id(id)?;
            context.assert_bit_width(pre.span, &ty, width);
            Ok(())
        }
        Constraint::IsPowerOfTwo => {
            if pre.operands.len() != 1 {
                return Err(WastError::new(
                    pre.span,
                    format!(
                        "the `is-power-of-two` precondition requires exactly 1 operand, found \
                         {} operands",
                        pre.operands.len(),
                    ),
                )
                .into());
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! verify_ok {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let buf = wast::parser::ParseBuffer::new($src).expect("should lex OK");
                let opts = match wast::parser::parse::<Optimizations>(&buf) {
                    Ok(opts) => opts,
                    Err(mut e) => {
                        e.set_path(Path::new(stringify!($name)));
                        e.set_text($src);
                        eprintln!("{}", e);
                        panic!("should parse OK")
                    }
                };
                match verify(&opts) {
                    Ok(_) => return,
                    Err(mut e) => {
                        e.set_path(Path::new(stringify!($name)));
                        e.set_text($src);
                        eprintln!("{}", e);
                        panic!("should verify OK")
                    }
                }
            }
        };
    }

    macro_rules! verify_err {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let buf = wast::parser::ParseBuffer::new($src).expect("should lex OK");
                let opts = match wast::parser::parse::<Optimizations>(&buf) {
                    Ok(opts) => opts,
                    Err(mut e) => {
                        e.set_path(Path::new(stringify!($name)));
                        e.set_text($src);
                        eprintln!("{}", e);
                        panic!("should parse OK")
                    }
                };
                match verify(&opts) {
                    Ok(_) => panic!("expected a verification error, but it verified OK"),
                    Err(mut e) => {
                        e.set_path(Path::new(stringify!($name)));
                        e.set_text($src);
                        eprintln!("{}", e);
                        return;
                    }
                }
            }
        };
    }

    verify_ok!(bool_0, "(=> true true)");
    verify_ok!(bool_1, "(=> false false)");
    verify_ok!(bool_2, "(=> true false)");
    verify_ok!(bool_3, "(=> false true)");

    verify_err!(bool_is_not_int_0, "(=> true 42)");
    verify_err!(bool_is_not_int_1, "(=> 42 true)");

    verify_ok!(
        bit_width_0,
        "
(=> (when (iadd $x $y)
          (bit-width $x 32)
          (bit-width $y 32))
    (iadd $x $y))
"
    );
    verify_err!(
        bit_width_1,
        "
(=> (when (iadd $x $y)
          (bit-width $x 32)
          (bit-width $y 64))
    (iadd $x $y))
"
    );
    verify_err!(
        bit_width_2,
        "
(=> (when (iconst $C)
          (bit-width $C))
    5)
"
    );
    verify_err!(
        bit_width_3,
        "
(=> (when (iconst $C)
          (bit-width 32 32))
    5)
"
    );
    verify_err!(
        bit_width_4,
        "
(=> (when (iconst $C)
          (bit-width $C $C))
    5)
"
    );
    verify_err!(
        bit_width_5,
        "
(=> (when (iconst $C)
          (bit-width $C2 32))
    5)
"
    );
    verify_err!(
        bit_width_6,
        "
(=> (when (iconst $C)
          (bit-width $C2 33))
    5)
"
    );

    verify_ok!(
        is_power_of_two_0,
        "
(=> (when (imul $x $C)
          (is-power-of-two $C))
    (ishl $x $(log2 $C)))
"
    );
    verify_err!(
        is_power_of_two_1,
        "
(=> (when (imul $x $C)
          (is-power-of-two))
    5)
"
    );
    verify_err!(
        is_power_of_two_2,
        "
(=> (when (imul $x $C)
          (is-power-of-two $C $C))
    5)
"
    );
    verify_ok!(
        is_power_of_two_3,
        "
(=> (when (imul $x $C)
          (is-power-of-two 4))
    5)
"
    );

    verify_ok!(pattern_ops_0, "(=> (iadd $x $C) 5)");
    verify_err!(pattern_ops_1, "(=> (iadd $x) 5)");
    verify_err!(pattern_ops_2, "(=> (iadd $x $y $z) 5)");

    verify_ok!(unquote_0, "(=> $C $(log2 $C))");
    verify_err!(unquote_1, "(=> (iadd $C $D) $(log2 $C $D))");
    verify_err!(unquote_2, "(=> $x $(log2))");

    verify_ok!(rhs_0, "(=> $x (iadd $x (iconst 0)))");
    verify_err!(rhs_1, "(=> $x (iadd $x))");
    verify_err!(rhs_2, "(=> $x (iadd $x 0 0))");
}
