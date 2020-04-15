//! Formatting a peephole optimizer's automata for GraphViz Dot.
//!
//! See also `crates/automata/src/dot.rs`.

use peepmatic_automata::dot::DotFmt;
use peepmatic_runtime::{
    cc::ConditionCode,
    integer_interner::IntegerInterner,
    linear,
    operator::Operator,
    paths::{PathId, PathInterner},
};
use std::convert::TryFrom;
use std::io::{self, Write};

#[derive(Debug)]
pub(crate) struct PeepholeDotFmt<'a>(pub(crate) &'a PathInterner, pub(crate) &'a IntegerInterner);

impl DotFmt<Option<u32>, linear::MatchOp, Vec<linear::Action>> for PeepholeDotFmt<'_> {
    fn fmt_transition(
        &self,
        w: &mut impl Write,
        from: Option<&linear::MatchOp>,
        input: &Option<u32>,
        _to: Option<&linear::MatchOp>,
    ) -> io::Result<()> {
        let from = from.expect("we should have match op for every state");
        if let Some(x) = input {
            match from {
                linear::MatchOp::Opcode { .. } => {
                    let opcode =
                        Operator::try_from(*x).expect("we shouldn't generate non-opcode edges");
                    write!(w, "{}", opcode)
                }
                linear::MatchOp::ConditionCode { .. } => {
                    let cc =
                        ConditionCode::try_from(*x).expect("we shouldn't generate non-CC edges");
                    write!(w, "{}", cc)
                }
                _ => write!(w, "{}", x),
            }
        } else {
            write!(w, "(else)")
        }
    }

    fn fmt_state(&self, w: &mut impl Write, op: &linear::MatchOp) -> io::Result<()> {
        use linear::MatchOp::*;

        write!(w, r#"<font face="monospace">"#)?;

        let p = p(self.0);
        match op {
            Opcode { path } => write!(w, "opcode @ {}", p(path))?,
            IsConst { path } => write!(w, "is-const? @ {}", p(path))?,
            IsPowerOfTwo { id } => write!(w, "is-power-of-two? $lhs{}", id.0)?,
            BitWidth { id } => write!(w, "bit-width $lhs{}", id.0)?,
            FitsInNativeWord { id } => write!(w, "fits-in-native-word $lhs{}", id.0)?,
            Eq { id, path } => write!(w, "eq? $lhs{} @ {}", id.0, p(path))?,
            IntegerValue { path } => write!(w, "integer-value @ {}", p(path))?,
            BooleanValue { path } => write!(w, "boolean-value @ {}", p(path))?,
            ConditionCode { path } => write!(w, "condition-code @ {}", p(path))?,
            Nop => write!(w, "nop")?,
        }

        writeln!(w, "</font>")
    }

    fn fmt_output(&self, w: &mut impl Write, actions: &Vec<linear::Action>) -> io::Result<()> {
        use linear::Action::*;

        if actions.is_empty() {
            return writeln!(w, "(none)");
        }

        write!(w, r#"<font face="monospace">"#)?;

        let p = p(self.0);

        for a in actions {
            match a {
                BindLhs { id, path } => write!(w, "$lhs{} = bind-lhs @ {}<br/>", id.0, p(path))?,
                GetLhsBinding { id } => write!(w, "get-lhs-binding $lhs{}<br/>", id.0)?,
                UnaryUnquote { operator, operand } => {
                    write!(w, "eval {} $rhs{}<br/>", operator, operand.0)?
                }
                BinaryUnquote { operator, operands } => write!(
                    w,
                    "eval {} $rhs{}, $rhs{}<br/>",
                    operator, operands[0].0, operands[1].0,
                )?,
                MakeIntegerConst { value } => write!(w, "{}<br/>", self.1.lookup(*value))?,
                MakeBooleanConst { value } => write!(w, "{}<br/>", value)?,
                MakeConditionCode { cc } => write!(w, "{}<br/>", cc)?,
                MakeUnaryInst {
                    operand, operator, ..
                } => write!(w, "make {} $rhs{}<br/>", operator, operand.0,)?,
                MakeBinaryInst { operands, operator } => write!(
                    w,
                    "make {} $rhs{}, $rhs{}<br/>",
                    operator, operands[0].0, operands[1].0,
                )?,
                MakeTernaryInst { operator, operands } => write!(
                    w,
                    "make {} $rhs{}, $rhs{}, $rhs{}<br/>",
                    operator, operands[0].0, operands[1].0, operands[2].0,
                )?,
            }
        }

        writeln!(w, "</font>")
    }
}

fn p<'a>(paths: &'a PathInterner) -> impl Fn(&PathId) -> String + 'a {
    move |path: &PathId| {
        let mut s = vec![];
        for b in paths.lookup(*path).0 {
            s.push(b.to_string());
        }
        s.join(".")
    }
}
