use crate::core::answer::Answer;
use crate::core::reference::Ref;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum PrimOp {
    IsZero,
    MkBox,
    BoxSet,
    BoxGet,
    INeg,
    IAdd,
    ISub,
}

impl PrimOp {
    pub unsafe fn apply(&self, mut args: impl Iterator<Item = Answer>) -> Answer {
        use PrimOp::*;
        match self {
            IsZero => {
                if args.next().unwrap().repr() == 0 {
                    Answer::from_bool(true)
                } else {
                    Answer::from_bool(false)
                }
            }
            MkBox => Answer::from_ref(Ref::new(args.next().unwrap())),
            BoxGet => *args.next().unwrap().as_ref(),
            BoxSet => {
                let the_box = args.next().unwrap().as_mut();
                let value = args.next().unwrap();
                *the_box = value;
                Answer::from_int(0)
            }
            INeg => Answer::from_int(-args.next().unwrap().as_int()),
            IAdd => Answer::from_int(args.next().unwrap().as_int() + args.next().unwrap().as_int()),
            ISub => Answer::from_int(args.next().unwrap().as_int() - args.next().unwrap().as_int()),
        }
    }

    pub fn n_args(&self) -> usize {
        use PrimOp::*;
        match self {
            IsZero => 1,
            MkBox => 1,
            BoxGet => 1,
            BoxSet => 2,
            INeg => 1,
            IAdd | ISub => 2,
        }
    }

    pub fn n_results(&self) -> usize {
        use PrimOp::*;
        match self {
            IsZero => 1,
            MkBox => 1,
            BoxGet => 1,
            BoxSet => 0,
            INeg => 1,
            IAdd | ISub => 1,
        }
    }

    pub fn is_branching(&self) -> bool {
        use PrimOp::*;
        match self {
            IsZero => true,
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
