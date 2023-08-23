use crate::core::answer::Answer;
use crate::core::reference::Ref;

#[derive(Debug, Copy, Clone)]
pub enum Env {
    Empty,
    Entry(Ref<str>, Answer, Ref<Env>),
}

impl Env {
    pub fn extend(&self, var: Ref<str>, val: Answer) -> Self {
        Env::Entry(var, val, Ref::new(self.clone()))
    }

    pub fn lookup(&self, var: &str) -> Answer {
        let mut env = self;
        loop {
            match env {
                Env::Empty => panic!("Unbound variable: {var}"),
                Env::Entry(v, val, _) if &**v == var => return *val,
                Env::Entry(_, _, next) => env = next,
            }
        }
    }
}
