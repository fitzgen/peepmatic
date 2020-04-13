//! Formatting a peephole optimizer's automata for GraphViz Dot.
//!
//! See also `crates/automata/src/dot.rs`.

use peepmatic_automata::dot::DotFmt;
use peepmatic_runtime::{
    integer_interner::IntegerInterner,
    linear,
    paths::{PathId, PathInterner},
};
use std::io::{self, Write};

#[derive(Debug)]
pub(crate) struct PeepholeDotFmt<'a>(pub(crate) &'a PathInterner, pub(crate) &'a IntegerInterner);

impl DotFmt<Option<u32>, linear::MatchOp, Vec<linear::Action>> for PeepholeDotFmt<'_> {
    fn fmt_alphabet(&self, w: &mut impl Write, ch: &Option<u32>) -> io::Result<()> {
        if let Some(x) = ch {
            write!(w, "{}", x)
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
                BindLhs { id, path } => write!(w, "bind-lhs $lhs{} @ {}<br/>", id.0, p(path))?,
                GetLhsBinding { id } => write!(w, "get-lhs-binding $lhs{}<br/>", id.0)?,
                Log2 { operand } => write!(w, "log2 $rhs{}<br/>", operand.0)?,
                MakeIntegerConst { value } => {
                    write!(w, "make-iconst {}<br/>", self.1.lookup(*value))?
                }
                MakeBooleanConst { value } => write!(w, "make-bconst {}<br/>", value)?,
                MakeAshr { operands } => write!(
                    w,
                    "make-ashr $rhs{}, $rhs{}<br/>",
                    operands[0].0, operands[1].0
                )?,
                MakeBor { operands } => write!(
                    w,
                    "make-bor $rhs{}, $rhs{}<br/>",
                    operands[0].0, operands[1].0
                )?,
                MakeIadd { operands } => write!(
                    w,
                    "make-iadd $rhs{}, $rhs{}<br/>",
                    operands[0].0, operands[1].0
                )?,
                MakeIaddImm { operands } => write!(
                    w,
                    "make-iadd-imm $rhs{}, $rhs{}<br/>",
                    operands[0].0, operands[1].0
                )?,
                MakeIconst { operand } => write!(w, "make-iconst $rhs{}<br/>", operand.0)?,
                MakeImul { operands } => write!(
                    w,
                    "make-imul $rhs{}, $rhs{}<br/>",
                    operands[0].0, operands[1].0
                )?,
                MakeImulImm { operands } => write!(
                    w,
                    "make-imul-imm $rhs{}, $rhs{}<br/>",
                    operands[0].0, operands[1].0
                )?,
                MakeIshl { operands } => write!(
                    w,
                    "make-ishl $rhs{}, $rhs{}<br/>",
                    operands[0].0, operands[1].0
                )?,
                MakeSshr { operands } => write!(
                    w,
                    "make-sshr $rhs{}, $rhs{}<br/>",
                    operands[0].0, operands[1].0
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
