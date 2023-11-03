use crate::core::answer::Answer;
use crate::core::ptr_tagging::{maybe_pointer, untag};
use crate::core::reference::Ref;
use std::io::Write;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum PrimOp {
    CorP,  // test for tagged or const datatype variants
    Untag, // convert constant-tag back to plain integer
    IsZero,
    MkBox,
    BoxSet,
    BoxGet,
    ISame,
    ILess,
    INeg,
    IAdd,
    ISub,
    IMul,
    IDiv,
    FSame,
    SSame,
    CallCC, // call with current continuation
    Throw,  // throw a value to a continuation
    ShowInt,
    ShowReal,
    ShowStr,
}

impl PrimOp {
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "const/ptr?" => Some(PrimOp::CorP),
            "untag" => Some(PrimOp::Untag),
            "zero?" => Some(PrimOp::IsZero),
            "make-box" => Some(PrimOp::MkBox),
            "box-set" => Some(PrimOp::BoxSet),
            "box-get" => Some(PrimOp::BoxGet),
            "=" => Some(PrimOp::ISame),
            "<" => Some(PrimOp::ILess),
            "~" => Some(PrimOp::INeg),
            "+" => Some(PrimOp::IAdd),
            "-" => Some(PrimOp::ISub),
            "*" => Some(PrimOp::IMul),
            "/" => Some(PrimOp::IDiv),
            "=f" => Some(PrimOp::FSame),
            "=s" => Some(PrimOp::SSame),
            "call/cc" => Some(PrimOp::CallCC),
            "throw" => Some(PrimOp::Throw),
            _ => None,
        }
    }
    pub fn to_str(&self) -> &'static str {
        match self {
            PrimOp::CorP => "const/ptr?",
            PrimOp::Untag => "untag",
            PrimOp::IsZero => "zero?",
            PrimOp::MkBox => "make-box",
            PrimOp::BoxSet => "box-set",
            PrimOp::BoxGet => "box-get",
            PrimOp::ISame => "=",
            PrimOp::ILess => "<",
            PrimOp::INeg => "~",
            PrimOp::IAdd => "+",
            PrimOp::ISub => "-",
            PrimOp::IMul => "*",
            PrimOp::IDiv => "/",
            PrimOp::FSame => "=f",
            PrimOp::SSame => "=s",
            PrimOp::CallCC => "call/cc",
            PrimOp::Throw => "throw",
            PrimOp::ShowInt => "show-int",
            PrimOp::ShowReal => "show-real",
            PrimOp::ShowStr => "show-string",
        }
    }

    pub unsafe fn apply(&self, args: Vec<Answer>, out: &mut impl Write) -> Answer {
        use PrimOp::*;
        match self {
            CorP => Answer::from_bool(maybe_pointer(args[0].repr())),
            Untag => Answer::from_usize(untag(args[0].repr())),
            IsZero => Answer::from_bool(args[0].repr() == 0),
            MkBox => Answer::from_ref(Ref::new(args[0])),
            BoxGet => *args[0].as_ref(),
            BoxSet => {
                let the_box = args[0].as_mut();
                let value = args[1];
                *the_box = value;
                Answer::from_int(0)
            }
            ISame => Answer::from_bool(args[0].as_int() == args[1].as_int()),
            ILess => Answer::from_bool(args[0].as_int() < args[1].as_int()),
            INeg => Answer::from_int(-args[0].as_int()),
            IAdd => Answer::from_int(args[0].as_int() + args[1].as_int()),
            ISub => Answer::from_int(args[0].as_int() - args[1].as_int()),
            IMul => Answer::from_int(args[0].as_int() * args[1].as_int()),
            IDiv => Answer::from_int(args[0].as_int() / args[1].as_int()),
            FSame => Answer::from_bool(args[0].as_float() == args[1].as_float()),
            SSame => Answer::from_bool(args[0].as_str() == args[1].as_str()),
            CallCC | Throw => panic!(
                "Cannot apply continuation primitives. They need special CPS transformation."
            ),
            ShowInt => {
                let x = args[0];
                write!(out, "{}", x.as_int()).unwrap();
                x
            }
            ShowReal => {
                let x = args[0];
                write!(out, "{}", x.as_float()).unwrap();
                x
            }
            ShowStr => {
                let x = args[0];
                write!(out, "{}", x.as_str()).unwrap();
                x
            }
        }
    }

    pub fn n_args(&self) -> usize {
        use PrimOp::*;
        match self {
            CorP => 1,
            Untag => 1,
            IsZero => 1,
            MkBox => 1,
            BoxGet => 1,
            BoxSet => 2,
            ISame | ILess => 2,
            INeg => 1,
            IAdd | ISub | IMul | IDiv => 2,
            FSame => 2,
            SSame => 2,
            CallCC => 1,
            Throw => 2,
            ShowInt | ShowReal | ShowStr => 1,
        }
    }

    pub fn n_results(&self) -> usize {
        use PrimOp::*;
        match self {
            CorP => 0,
            Untag => 1,
            IsZero => 0,
            MkBox => 1,
            BoxGet => 1,
            BoxSet => 0,
            ISame | ILess => 0,
            INeg => 1,
            IAdd | ISub | IMul | IDiv => 1,
            FSame => 0,
            SSame => 0,
            CallCC => 1,
            Throw => 0,
            ShowInt | ShowReal | ShowStr => 1,
        }
    }

    pub fn is_branching(&self) -> bool {
        use PrimOp::*;
        match self {
            CorP | IsZero | ISame | ILess | FSame | SSame => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    #[test]
    fn boxes() {
        let mut cc = Cursor::new(vec![]);
        unsafe {
            let boxed = PrimOp::MkBox.apply(vec![Answer::from_int(123)], &mut cc);
            assert_eq!(PrimOp::BoxGet.apply(vec![boxed], &mut cc).as_int(), 123);
            PrimOp::BoxSet.apply(vec![boxed, Answer::from_int(42)], &mut cc);
            assert_eq!(PrimOp::BoxGet.apply(vec![boxed], &mut cc).as_int(), 42);
        }
    }
}
