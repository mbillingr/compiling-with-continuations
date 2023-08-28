use crate::core::answer::Answer;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum PrimOp {
    INeg,
    IAdd,
    ISub,
}

impl PrimOp {
    pub fn apply(&self, mut args: impl Iterator<Item = Answer>) -> Answer {
        use PrimOp::*;
        match self {
            INeg => Answer::from_int(-args.next().unwrap().as_int()),
            IAdd => Answer::from_int(args.next().unwrap().as_int() + args.next().unwrap().as_int()),
            ISub => Answer::from_int(args.next().unwrap().as_int() - args.next().unwrap().as_int()),
        }
    }
    pub fn n_args(&self) -> usize {
        use PrimOp::*;
        match self {
            INeg => 1,
            IAdd | ISub => 2,
        }
    }
    pub fn n_results(&self) -> usize {
        use PrimOp::*;
        match self {
            INeg => 1,
            IAdd | ISub => 1,
        }
    }
}
