use crate::languages::cps_lang::ast::{AccessPath, Expr, Value};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

// special registers
const CNT: &'static str = "cnt";
const TMP: &'static str = "tmp";

const STANDARD_ARG_REGISTERS: &'static [&'static str] = &["r0", "r1", "r2"];

pub fn program_to_c<V: Clone + Eq + Hash + std::fmt::Debug + std::fmt::Display>(
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

impl<V: Clone + Eq + Hash + std::fmt::Debug + std::fmt::Display> Context<V> {
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
                stmts = self.shuffle_registers(arg_registers, rands, stmts);
                self.c_static_tailcall(f, stmts)
            }

            Expr::App(rator, rands) => {
                stmts = self.shuffle_registers(STANDARD_ARG_REGISTERS, rands, stmts);
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

    fn shuffle_registers(
        &self,
        targets: &[impl std::fmt::Display],
        values: &[Value<V>],
        mut stmts: Vec<String>,
    ) -> Vec<String> {
        todo!()
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
