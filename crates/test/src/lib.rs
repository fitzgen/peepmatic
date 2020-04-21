//! Testing utilities and a testing-only instruction set for `peepmatic`.

#![deny(missing_debug_implementations)]

use peepmatic_runtime::{
    cc::ConditionCode,
    instruction_set::InstructionSet,
    operator::Operator,
    part::{Constant, Part},
    paths::Path,
    r#type::{BitWidth, Kind, Type},
};
use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Instruction(pub usize);

#[derive(Debug)]
pub struct InstructionData {
    pub operator: Operator,
    pub r#type: Type,
    pub immediates: Vec<Immediate>,
    pub arguments: Vec<Instruction>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Immediate {
    Constant(Constant),
    ConditionCode(ConditionCode),
}

impl Immediate {
    fn unwrap_constant(&self) -> Constant {
        match *self {
            Immediate::Constant(c) => c,
            _ => panic!("not a constant"),
        }
    }
}

impl From<Constant> for Immediate {
    fn from(c: Constant) -> Immediate {
        Immediate::Constant(c)
    }
}

impl From<ConditionCode> for Immediate {
    fn from(cc: ConditionCode) -> Immediate {
        Immediate::ConditionCode(cc)
    }
}

impl From<Immediate> for Part<Instruction> {
    fn from(imm: Immediate) -> Part<Instruction> {
        match imm {
            Immediate::Constant(c) => Part::Constant(c),
            Immediate::ConditionCode(cc) => Part::ConditionCode(cc),
        }
    }
}

impl TryFrom<Part<Instruction>> for Immediate {
    type Error = &'static str;

    fn try_from(part: Part<Instruction>) -> Result<Immediate, Self::Error> {
        match part {
            Part::Constant(c) => Ok(Immediate::Constant(c)),
            Part::ConditionCode(c) => Ok(Immediate::ConditionCode(c)),
            Part::Instruction(_) => Err("instruction parts cannot be converted into immediates"),
        }
    }
}

#[derive(Debug, Default)]
pub struct Program {
    instr_counter: usize,
    instruction_data: HashMap<Instruction, InstructionData>,
    replacements: RefCell<HashMap<Instruction, Instruction>>,
}

impl Program {
    /// Are `a` and `b` structurally equivalent, even if they use different
    /// `Instruction`s for various arguments?
    pub fn structurally_eq(&mut self, a: Instruction, b: Instruction) -> bool {
        macro_rules! ensure_eq {
            ($a:expr, $b:expr) => {{
                let a = &$a;
                let b = &$b;
                if a != b {
                    log::debug!(
                        "{} != {} ({:?} != {:?})",
                        stringify!($a),
                        stringify!($b),
                        a,
                        b
                    );
                    return false;
                }
            }};
        }

        let a = self.resolve(a);
        let b = self.resolve(b);
        if a == b {
            return true;
        }

        let a = self.data(a);
        let b = self.data(b);
        log::debug!("structurally_eq({:?}, {:?})", a, b);

        ensure_eq!(a.operator, b.operator);
        ensure_eq!(a.r#type, b.r#type);
        ensure_eq!(a.immediates, b.immediates);
        ensure_eq!(a.arguments.len(), b.arguments.len());
        a.arguments
            .clone()
            .into_iter()
            .zip(b.arguments.clone().into_iter())
            .all(|(a, b)| self.structurally_eq(a, b))
    }

    pub fn replace_instruction(&mut self, old: Instruction, new: Instruction) {
        let mut replacements = self.replacements.borrow_mut();
        let existing_replacement = replacements.insert(old, new);
        assert!(existing_replacement.is_none());

        let old_data = self.instruction_data.remove(&old);
        assert!(old_data.is_some());
    }

    pub fn resolve(&self, inst: Instruction) -> Instruction {
        let mut replacements = self.replacements.borrow_mut();
        let mut replacements_followed = 0;
        let mut resolved = inst;
        while let Some(i) = replacements.get(&resolved).cloned() {
            replacements_followed += 1;
            assert!(replacements_followed <= replacements.len());
            resolved = i;
            continue;
        }

        if inst != resolved {
            let old_replacement = replacements.insert(inst, resolved);
            assert!(old_replacement.is_some());
        }

        resolved
    }

    pub fn data(&self, inst: Instruction) -> &InstructionData {
        let inst = self.resolve(inst);
        &self.instruction_data[&inst]
    }

    pub fn new_instruction(
        &mut self,
        operator: Operator,
        r#type: Type,
        immediates: Vec<Immediate>,
        arguments: Vec<Instruction>,
    ) -> Instruction {
        assert_eq!(
            operator.immediates_arity() as usize,
            immediates.len(),
            "wrong number of immediates for {:?}: expected {}, found {}",
            operator,
            operator.immediates_arity(),
            immediates.len(),
        );
        assert_eq!(
            operator.params_arity() as usize,
            arguments.len(),
            "wrong number of arguments for {:?}: expected {}, found {}",
            operator,
            operator.params_arity(),
            arguments.len(),
        );

        assert!(!r#type.bit_width.is_polymorphic());
        assert!(immediates.iter().all(|imm| match imm {
            Immediate::Constant(Constant::Bool(_, w))
            | Immediate::Constant(Constant::Int(_, w)) => !w.is_polymorphic(),
            Immediate::ConditionCode(_) => true,
        }));

        let inst = Instruction(self.instr_counter);
        self.instr_counter += 1;

        let data = InstructionData {
            operator,
            r#type,
            immediates,
            arguments,
        };

        log::trace!("new instruction: {:?} = {:?}", inst, data);
        self.instruction_data.insert(inst, data);
        inst
    }

    pub fn r#const(&mut self, c: Constant, root_bit_width: BitWidth) -> Instruction {
        assert!(!root_bit_width.is_polymorphic());
        match c {
            Constant::Bool(_, bit_width) => self.new_instruction(
                Operator::Bconst,
                if bit_width.is_polymorphic() {
                    Type {
                        kind: Kind::Bool,
                        bit_width: root_bit_width,
                    }
                } else {
                    Type {
                        kind: Kind::Bool,
                        bit_width,
                    }
                },
                vec![c.into()],
                vec![],
            ),
            Constant::Int(_, bit_width) => self.new_instruction(
                Operator::Iconst,
                if bit_width.is_polymorphic() {
                    Type {
                        kind: Kind::Int,
                        bit_width: root_bit_width,
                    }
                } else {
                    Type {
                        kind: Kind::Int,
                        bit_width,
                    }
                },
                vec![c.into()],
                vec![],
            ),
        }
    }

    fn instruction_to_constant(&mut self, inst: Instruction) -> Option<Constant> {
        match self.data(inst) {
            InstructionData {
                operator: Operator::Iconst,
                immediates,
                ..
            } => Some(immediates[0].unwrap_constant()),
            InstructionData {
                operator: Operator::Bconst,
                immediates,
                ..
            } => Some(immediates[0].unwrap_constant()),
            _ => None,
        }
    }

    fn part_to_immediate(&mut self, part: Part<Instruction>) -> Result<Immediate, &'static str> {
        match part {
            Part::Instruction(i) => self
                .instruction_to_constant(i)
                .map(|c| c.into())
                .ok_or("non-constant instructions cannot be converted into immediates"),
            Part::Constant(c) => Ok(c.into()),
            Part::ConditionCode(cc) => Ok(Immediate::ConditionCode(cc)),
        }
    }

    fn part_to_instruction(
        &mut self,
        root: Instruction,
        part: Part<Instruction>,
    ) -> Result<Instruction, &'static str> {
        match part {
            Part::Instruction(inst) => {
                let inst = self.resolve(inst);
                Ok(inst)
            }
            Part::Constant(c) => {
                let root_width = self.data(root).r#type.bit_width;
                Ok(self.r#const(c, root_width))
            }
            Part::ConditionCode(_) => Err("condition codes cannot be converted into instructions"),
        }
    }
}

#[derive(Debug)]
pub struct TestIsa {
    pub native_word_size_in_bits: u8,
}

impl<'a> InstructionSet<'a> for TestIsa {
    type Context = Program;

    type Instruction = Instruction;

    fn replace_instruction(
        &self,
        program: &mut Program,
        old: Instruction,
        new: Part<Instruction>,
    ) -> Instruction {
        log::debug!("replace_instruction({:?}, {:?})", old, new);
        let old = program.resolve(old);
        let new = program.part_to_instruction(old, new).unwrap();
        program.replace_instruction(old, new);
        new
    }

    fn get_part_at_path(
        &self,
        program: &mut Program,
        root: Instruction,
        path: Path,
    ) -> Option<Part<Instruction>> {
        log::debug!("get_part_at_path({:?})", path);

        assert!(!path.0.is_empty());
        assert_eq!(path.0[0], 0);

        let mut part = Part::Instruction(root);
        for p in &path.0[1..] {
            if let Part::Instruction(inst) = part {
                let data = program.data(inst);
                let p = *p as usize;

                if p < data.immediates.len() {
                    part = data.immediates[p].into();
                    continue;
                }

                if let Some(inst) = data.arguments.get(p - data.immediates.len()).copied() {
                    part = Part::Instruction(inst);
                    continue;
                }
            }

            return None;
        }

        Some(part)
    }

    fn operator(&self, program: &mut Program, instr: Instruction) -> Option<Operator> {
        log::debug!("operator({:?})", instr);
        let data = program.data(instr);
        Some(data.operator)
    }

    fn make_inst_1(
        &self,
        program: &mut Program,
        root: Instruction,
        operator: Operator,
        r#type: Type,
        a: Part<Instruction>,
    ) -> Instruction {
        log::debug!(
            "make_inst_1(\n\toperator = {:?},\n\ttype = {},\n\ta = {:?},\n)",
            operator,
            r#type,
            a,
        );

        let (imms, args) = match operator.immediates_arity() {
            0 => {
                assert_eq!(operator.params_arity(), 1);
                (vec![], vec![program.part_to_instruction(root, a).unwrap()])
            }
            1 => {
                assert_eq!(operator.params_arity(), 0);
                (vec![a.try_into().unwrap()], vec![])
            }
            _ => unreachable!(),
        };
        program.new_instruction(operator, r#type, imms, args)
    }

    fn make_inst_2(
        &self,
        program: &mut Program,
        root: Instruction,
        operator: Operator,
        r#type: Type,
        a: Part<Instruction>,
        b: Part<Instruction>,
    ) -> Instruction {
        log::debug!(
            "make_inst_2(\n\toperator = {:?},\n\ttype = {},\n\ta = {:?},\n\tb = {:?},\n)",
            operator,
            r#type,
            a,
            b,
        );

        let (imms, args) = match operator.immediates_arity() {
            0 => {
                assert_eq!(operator.params_arity(), 2);
                (
                    vec![],
                    vec![
                        program.part_to_instruction(root, a).unwrap(),
                        program.part_to_instruction(root, b).unwrap(),
                    ],
                )
            }
            1 => {
                assert_eq!(operator.params_arity(), 1);
                (
                    vec![program.part_to_immediate(a).unwrap()],
                    vec![program.part_to_instruction(root, b).unwrap()],
                )
            }
            2 => {
                assert_eq!(operator.params_arity(), 0);
                (
                    vec![
                        program.part_to_immediate(a).unwrap(),
                        program.part_to_immediate(b).unwrap(),
                    ],
                    vec![],
                )
            }
            _ => unreachable!(),
        };
        program.new_instruction(operator, r#type, imms, args)
    }

    fn make_inst_3(
        &self,
        program: &mut Program,
        root: Instruction,
        operator: Operator,
        r#type: Type,
        a: Part<Instruction>,
        b: Part<Instruction>,
        c: Part<Instruction>,
    ) -> Instruction {
        log::debug!(
            "make_inst_3(\n\toperator = {:?},\n\ttype = {},\n\ta = {:?},\n\tb = {:?},\n\tc = {:?},\n)",
            operator,
            r#type,
            a,
            b,
            c,
        );
        let (imms, args) = match operator.immediates_arity() {
            0 => {
                assert_eq!(operator.params_arity(), 3);
                (
                    vec![],
                    vec![
                        program.part_to_instruction(root, a).unwrap(),
                        program.part_to_instruction(root, b).unwrap(),
                        program.part_to_instruction(root, c).unwrap(),
                    ],
                )
            }
            1 => {
                assert_eq!(operator.params_arity(), 2);
                (
                    vec![program.part_to_immediate(a).unwrap()],
                    vec![
                        program.part_to_instruction(root, b).unwrap(),
                        program.part_to_instruction(root, c).unwrap(),
                    ],
                )
            }
            2 => {
                assert_eq!(operator.params_arity(), 1);
                (
                    vec![
                        program.part_to_immediate(a).unwrap(),
                        program.part_to_immediate(b).unwrap(),
                    ],
                    vec![program.part_to_instruction(root, c).unwrap()],
                )
            }
            3 => {
                assert_eq!(operator.params_arity(), 0);
                (
                    vec![
                        program.part_to_immediate(a).unwrap(),
                        program.part_to_immediate(b).unwrap(),
                        program.part_to_immediate(c).unwrap(),
                    ],
                    vec![],
                )
            }
            _ => unreachable!(),
        };
        program.new_instruction(operator, r#type, imms, args)
    }

    fn instruction_to_constant(
        &self,
        program: &mut Program,
        inst: Instruction,
    ) -> Option<Constant> {
        log::debug!("instruction_to_constant({:?})", inst);
        program.instruction_to_constant(inst)
    }

    fn instruction_result_bit_width(&self, program: &mut Program, inst: Instruction) -> u8 {
        log::debug!("instruction_result_bit_width({:?})", inst);
        let ty = program.data(inst).r#type;
        ty.bit_width.fixed_width().unwrap()
    }

    fn native_word_size_in_bits(&self, _program: &mut Program) -> u8 {
        log::debug!("native_word_size_in_bits");
        self.native_word_size_in_bits
    }
}
