use crate::languages::cps_lang::ast::{Expr, Value};

const INDENT: usize = 2;

impl<V: std::fmt::Display> Expr<V> {
    pub fn pretty_print(&self) {
        self.pretty_print_(0);
    }

    fn pretty_print_(&self, indent: usize) {
        match self {
            Expr::Record(fields, var, cnt) => {
                print!("{var} := [");
                for (i, (x, _)) in fields.iter().enumerate() {
                    if i > 0 {
                        print!(" ")
                    }
                    x.pretty_print()
                }
                println!("]");
                print!("{: >1$}", "", indent);
                cnt.pretty_print_(indent);
            }

            Expr::Select(idx, rec, var, cnt) => {
                print!("{var} := ");
                rec.pretty_print();
                println!("[{idx}]");
                print!("{: >1$}", "", indent);
                cnt.pretty_print_(indent);
            }

            Expr::Offset(idx, rec, var, cnt) => {
                print!("{var} := ");
                rec.pretty_print();
                println!("[{idx}..] ");
                print!("{: >1$}", "", indent);
                cnt.pretty_print_(indent);
            }

            Expr::App(rator, rands) => {
                print!("(");
                rator.pretty_print();
                for x in rands.iter() {
                    print!(" ");
                    x.pretty_print()
                }
                print!(")");
            }

            Expr::Fix(defs, body) => {
                println!("fix");
                for (f, params, fbody) in defs.iter() {
                    print!("{: >1$}({f}", "", indent + INDENT);
                    for p in params.iter() {
                        print!(" {p}");
                    }
                    println!(") = ");
                    print!("{: >1$}", "", indent + INDENT * 2);
                    fbody.pretty_print_(indent + INDENT * 2);
                    println!();
                }
                print!("{: >1$}", "", indent);
                body.pretty_print_(indent);
            }

            Expr::Switch(val, arms) => {
                print!("switch ");
                val.pretty_print();
                for (i, cnt) in arms.iter().enumerate() {
                    println!();
                    println!("{: >1$}case {i}:", "", indent + INDENT);
                    print!("{: >1$}", "", indent + INDENT * 2);
                    cnt.pretty_print_(indent + INDENT * 2);
                }
            }

            Expr::PrimOp(op, args, vars, cnt) => {
                print!("[");
                for (i, v) in vars.iter().enumerate() {
                    if i > 0 {
                        print!(" ")
                    }
                    print!("{v}")
                }
                print!("] := ({op:?}");
                for a in args.iter() {
                    print!(" ");
                    a.pretty_print();
                }
                print!(")");

                if cnt.len() == 1 {
                    println!();
                    print!("{: >1$}", "", indent);
                    cnt[0].pretty_print_(indent);
                } else {
                    for c in cnt.iter() {
                        println!();
                        println!("{: >1$}case:", "", indent + INDENT);
                        print!("{: >1$}", "", indent + INDENT * 2);
                        c.pretty_print_(indent + INDENT * 2);
                    }
                }
            }

            Expr::Halt(value) => {
                print!("halt ");
                value.pretty_print();
            }

            Expr::Panic(msg) => {
                println!("panic {msg:?}");
            }
        }
    }
}

impl<V: std::fmt::Display> Value<V> {
    pub fn pretty_print(&self) {
        match self {
            Value::Var(x) => print!("{}", x),
            Value::Label(x) => print!("@{}", x),
            Value::Int(x) => print!("{}", x),
            Value::Real(x) => print!("{}", x),
            Value::String(x) => print!("{:?}", x),
        }
    }
}
