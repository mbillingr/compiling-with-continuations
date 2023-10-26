use crate::languages::cps_lang::ast::{AccessPath, Expr, Value};
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::ops::Deref;

// special registers
const CNT: &'static str = "cnt";
const TMP: &'static str = "tmp";

const STANDARD_ARG_REGISTERS: &'static [&'static str] = &["r0", "r1", "r2"];

pub fn program_to_c<
    V: Clone + Eq + Hash + Borrow<str> + Deref<Target = str> + std::fmt::Debug + std::fmt::Display,
>(
    expr: &Expr<V>,
) -> Vec<String> {
    let mut ctx = Context::new();
    let main = ctx.generate_c(expr, vec![]);
    main
}

pub struct Context<V> {
    registers: HashSet<V>,
    functions: HashMap<V, KnownFunction<V>>,
}

impl<
        V: Clone + Eq + Hash + Borrow<str> + Deref<Target = str> + std::fmt::Debug + std::fmt::Display,
    > Context<V>
{
    pub fn new() -> Self {
        Context {
            registers: Default::default(),
            functions: Default::default(),
        }
    }

    fn generate_c(&mut self, expr: &Expr<V>, mut stmts: Vec<String>) -> Vec<String> {
        match expr {
            Expr::Record(fields, var, cnt) => {
                stmts = self.c_begin_record(fields.len(), stmts);
                for (val, ap) in fields.iter() {
                    let x = self.generate_access(val, ap);
                    stmts = self.c_push_field(x, stmts);
                }
                stmts = self.c_end_record(var, stmts);
                self.generate_c(cnt, stmts)
            }

            Expr::Select(idx, rec, var, cnt) => {
                let r = self.generate_value(rec);
                stmts = self.c_select(*idx, r, var, stmts);
                self.generate_c(cnt, stmts)
            }

            Expr::Offset(idx, rec, var, cnt) => {
                let r = self.generate_value(rec);
                stmts = self.c_offset(*idx, r, var, stmts);
                self.generate_c(cnt, stmts)
            }

            Expr::App(Value::Label(f), rands) => {
                let arg_registers = self.functions[f].arg_registers.as_ref();
                stmts = self.set_values(arg_registers, rands, stmts);
                self.c_static_tailcall(f, stmts)
            }

            Expr::App(rator, rands) => {
                stmts = self.set_values(STANDARD_ARG_REGISTERS, rands, stmts);
                let f = self.generate_value(rator);
                self.c_dynamic_tailcall(f, stmts)
            }

            Expr::Fix(defs, cnt) => {
                for (f, p, _) in defs.iter() {
                    self.functions.insert(f.clone(), KnownFunction::new(p));
                }

                let mut stmts = self.generate_c(cnt, stmts);

                for (f, p, body) in defs.iter() {
                    stmts = self.c_begin_function(f, stmts);
                    stmts = self.generate_c(body, stmts);
                }
                stmts
            }

            Expr::Halt(value) => {
                let value = self.generate_value(value);
                self.c_halt(value, stmts)
            }

            _ => todo!("{expr:?}"),
        }
    }

    fn generate_value(&self, value: &Value<V>) -> String {
        match value {
            Value::Int(i) => i.to_string(),
            Value::Real(r) => r.to_string(),
            Value::String(s) => format!("{:?}", s),
            Value::Var(v) => v.to_string(),
            Value::Label(v) => format!("&&{v}"),
            _ => todo!("{value:?}"),
        }
    }

    fn generate_access(&self, value: &Value<V>, ap: &AccessPath) -> String {
        match ap {
            AccessPath::Ref(0) => self.generate_value(value),
            AccessPath::Ref(i) => todo!(),
            AccessPath::Sel(i, ap) => format!("{}[{}]", self.generate_access(value, ap), i),
        }
    }

    fn set_values(
        &self,
        targets: &[impl std::fmt::Display],
        values: &[Value<V>],
        mut stmts: Vec<String>,
    ) -> Vec<String> {
        let mut pending_copies: Vec<_> = Default::default();

        for (tgt, v) in targets.iter().zip(values) {
            match v {
                Value::Var(r) => {
                    let r = r.to_string();
                    let tgt = tgt.to_string();
                    if r != tgt {
                        pending_copies.push((r, tgt));
                    }
                }
                _ => {
                    stmts = self.c_set_register(tgt, self.generate_value(v), stmts);
                }
            }
        }

        let actual_copies = Self::shuffle_registers(pending_copies);

        for (src, tgt) in actual_copies {
            stmts = self.c_set_register(tgt, src, stmts);
        }

        stmts
    }

    fn shuffle_registers(mut pending_copies: Vec<(String, String)>) -> Vec<(String, String)> {
        let mut actual_copies = vec![];

        while pending_copies.len() > 0 {
            // copy into all unoccupied target registers
            let mut i = 0;
            while i < pending_copies.len() {
                let (_, tgt) = &pending_copies[i];
                if pending_copies.iter().find(|(s, _)| s == tgt).is_none() {
                    let (src, tgt) = pending_copies.swap_remove(i);
                    actual_copies.push((src.clone(), tgt.clone()));

                    // make src available as target by replacing all other occurrences of src
                    for (s, t) in pending_copies.iter_mut() {
                        if s == &src {
                            *s = tgt.clone();
                        }
                    }
                    i = 0;
                } else {
                    i += 1;
                }
            }

            if pending_copies.len() > 0 {
                let (src, tgt) = pending_copies.pop().unwrap();
                pending_copies.push((TMP.to_string(), tgt.to_string()));
                actual_copies.push((tgt.clone(), TMP.to_string()));
                actual_copies.push((src.clone(), tgt.clone()));
                // make src available as target by replacing all other occurrences of src
                for (s, t) in pending_copies.iter_mut() {
                    if s == &src {
                        *s = tgt.clone();
                    }
                }
            }
        }
        actual_copies
    }

    fn c_set_register(
        &self,
        r: impl std::fmt::Display,
        src: impl std::fmt::Display,
        mut stmts: Vec<String>,
    ) -> Vec<String> {
        stmts.push(format!("{r} = {src};"));
        stmts
    }

    fn c_halt(&self, value: String, mut stmts: Vec<String>) -> Vec<String> {
        stmts.push(format!("return {value};"));
        stmts
    }

    fn c_begin_function(&self, name: &V, mut stmts: Vec<String>) -> Vec<String> {
        stmts.push(format!("{name}:"));
        stmts
    }

    fn c_begin_record(&self, len: usize, mut stmts: Vec<String>) -> Vec<String> {
        stmts.push(format!("{TMP} = NEW_RECORD({len});"));
        stmts.push(format!("{CNT} = 0;"));
        stmts
    }

    fn c_push_field(&self, value: String, mut stmts: Vec<String>) -> Vec<String> {
        stmts.push(format!("{TMP}[{CNT}++] = {value};"));
        stmts
    }

    fn c_end_record(&self, r: impl std::fmt::Display, mut stmts: Vec<String>) -> Vec<String> {
        stmts.push(format!("{r} = {TMP};"));
        stmts
    }

    fn c_select(
        &self,
        idx: isize,
        rec: String,
        var: impl std::fmt::Display,
        mut stmts: Vec<String>,
    ) -> Vec<String> {
        stmts.push(format!("{var} = {rec}[{idx}];"));
        stmts
    }

    fn c_offset(
        &self,
        idx: isize,
        rec: String,
        var: impl std::fmt::Display,
        mut stmts: Vec<String>,
    ) -> Vec<String> {
        stmts.push(format!("{var} = {rec} + {idx};"));
        stmts
    }

    fn c_dynamic_tailcall(&self, f: String, mut stmts: Vec<String>) -> Vec<String> {
        stmts.push(format!("goto *{f};"));
        stmts
    }

    fn c_static_tailcall(
        &self,
        label: impl std::fmt::Display,
        mut stmts: Vec<String>,
    ) -> Vec<String> {
        stmts.push(format!("goto {label};"));
        stmts
    }
}

struct KnownFunction<V> {
    arg_registers: Vec<V>,
}

impl<V: Clone> KnownFunction<V> {
    fn new(params: &[V]) -> Self {
        KnownFunction {
            arg_registers: params.to_vec(),
        }
    }
}

fn pop<K: Eq + Hash + Clone, V>(map: &mut HashMap<K, V>) -> Option<(K, V)> {
    let (k, _) = map.iter().next()?;
    let k = k.clone();
    map.remove(&k).map(|v| (k, v))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_shuffling_to_do() {
        assert_eq!(Context::<&str>::shuffle_registers(vec![]), vec![]);
    }

    #[test]
    fn shuffle_into_multiple_registers() {
        assert_eq!(
            Context::<&str>::shuffle_registers(
                [("a", "b"), ("a", "c"), ("a", "d")]
                    .iter()
                    .map(|(s, t)| (s.to_string(), t.to_string()))
                    .collect(),
            ),
            [("a", "b"), ("b", "d"), ("d", "c")]
                .iter()
                .map(|(s, t)| (s.to_string(), t.to_string()))
                .collect::<Vec<_>>()
        )
    }

    #[test]
    fn shuffle_cycle() {
        todo!()
    }

    #[test]
    fn shuffle_multiple_cycle() {
        todo!()
    }
}
