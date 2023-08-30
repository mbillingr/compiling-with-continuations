use crate::core::answer::Answer;
use crate::core::reference::Ref;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum PrimOp {
    IsZero,
    MkBox,
    BoxSet,
    BoxGet,
    ISame,
    INeg,
    IAdd,
    ISub,
    FSame,
    SSame,
}

impl PrimOp {
    pub unsafe fn apply(&self, mut args: impl Iterator<Item = Answer>) -> Answer {
        use PrimOp::*;
        match self {
            IsZero => Answer::from_bool(args.next().unwrap().repr() == 0),
            MkBox => Answer::from_ref(Ref::new(args.next().unwrap())),
            BoxGet => *args.next().unwrap().as_ref(),
            BoxSet => {
                let the_box = args.next().unwrap().as_mut();
                let value = args.next().unwrap();
                *the_box = value;
                Answer::from_int(0)
            }
            ISame => {
                Answer::from_bool(args.next().unwrap().as_int() == args.next().unwrap().as_int())
            }
            INeg => Answer::from_int(-args.next().unwrap().as_int()),
            IAdd => Answer::from_int(args.next().unwrap().as_int() + args.next().unwrap().as_int()),
            ISub => Answer::from_int(args.next().unwrap().as_int() - args.next().unwrap().as_int()),
            FSame => Answer::from_bool(
                args.next().unwrap().as_float() == args.next().unwrap().as_float(),
            ),
            SSame => {
                Answer::from_bool(args.next().unwrap().as_str() == args.next().unwrap().as_str())
            }
        }
    }

    pub fn n_args(&self) -> usize {
        use PrimOp::*;
        match self {
            IsZero => 1,
            MkBox => 1,
            BoxGet => 1,
            BoxSet => 2,
            ISame => 2,
            INeg => 1,
            IAdd | ISub => 2,
            FSame => 2,
            SSame => 2,
        }
    }

    pub fn n_results(&self) -> usize {
        use PrimOp::*;
        match self {
            IsZero => 0,
            MkBox => 1,
            BoxGet => 1,
            BoxSet => 0,
            ISame => 0,
            INeg => 1,
            IAdd | ISub => 1,
            FSame => 0,
            SSame => 0,
        }
    }

    pub fn is_branching(&self) -> bool {
        use PrimOp::*;
        match self {
            IsZero | ISame | FSame | SSame => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn boxes() {
        unsafe {
            let boxed = PrimOp::MkBox.apply(vec![Answer::from_int(123)].into_iter());
            assert_eq!(PrimOp::BoxGet.apply(vec![boxed].into_iter()).as_int(), 123);
            PrimOp::BoxSet.apply(vec![boxed, Answer::from_int(42)].into_iter());
            assert_eq!(PrimOp::BoxGet.apply(vec![boxed].into_iter()).as_int(), 42);
        }
    }
}
