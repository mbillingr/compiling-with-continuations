use crate::core::answer::Answer;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Unary {
    INeg,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Binary {
    IAdd,
    ISub,
}

impl Unary {
    pub fn apply(&self, x: Answer) -> Answer {
        match self {
            Unary::INeg => Answer::from_int(-x.as_int()),
        }
    }

    pub fn n_args(&self) -> usize {
        1
    }
    pub fn n_results(&self) -> usize {
        match self {
            Unary::INeg => 1,
        }
    }
}

impl Binary {
    pub fn apply(&self, a: Answer, b: Answer) -> Answer {
        match self {
            Binary::IAdd => Answer::from_int(a.as_int() + b.as_int()),
            Binary::ISub => Answer::from_int(a.as_int() - b.as_int()),
        }
    }

    pub fn n_args(&self) -> usize {
        2
    }
    pub fn n_results(&self) -> usize {
        1
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum PrimOp {
    Unary(Unary),
    Binary(Binary),
}

impl PrimOp {
    pub fn apply(&self, mut args: impl Iterator<Item = Answer>) -> Answer {
        match self {
            PrimOp::Unary(op) => op.apply(args.next().unwrap()),
            PrimOp::Binary(op) => {
                let a = args.next().unwrap();
                let b = args.next().unwrap();
                op.apply(a, b)
            }
        }
    }
    pub fn n_args(&self) -> usize {
        match self {
            PrimOp::Unary(op) => op.n_args(),
            PrimOp::Binary(op) => op.n_args(),
        }
    }
    pub fn n_results(&self) -> usize {
        match self {
            PrimOp::Unary(op) => op.n_results(),
            PrimOp::Binary(op) => op.n_results(),
        }
    }
}
