use crate::core::answer::Answer;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Unary {
    INeg,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Binary {
    ISub,
}

impl Unary {
    pub fn apply(&self, x: Answer) -> Answer {
        match self {
            Unary::INeg => Answer::from_int(-x.as_int()),
        }
    }
}

impl Binary {
    pub fn apply(&self, a: Answer, b: Answer) -> Answer {
        match self {
            Binary::ISub => Answer::from_int(a.as_int() - b.as_int()),
        }
    }
}
