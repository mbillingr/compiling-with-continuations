use crate::transformations::GensymContext;
use std::sync::Arc;
macro_rules! make_testsuite_for_type_lang {
    ($run:path) => {
        #[test]
        fn constants() {
            assert_eq!($run("(show 42)", ""), "42");
            assert_eq!($run("(show 12.34)", ""), "12.34");
            assert_eq!($run("(show \"äöü\")", ""), "äöü");
        }

        #[test]
        fn enum_instantiation() {
            assert_eq!(
                $run("(define ((enum (Foo) A B)) (show (Foo . A)))", ""),
                "A"
            );

            assert_eq!(
                $run(
                    "(define ((enum (Foo) A (B Int) C)) (show ((Foo . B) 42)))",
                    ""
                ),
                "(B 42)"
            );

            assert_eq!(
                $run("(define ((enum (Foo T) A B)) (show ((Foo Int) . A)))", ""),
                "A"
            );

            assert_eq!(
                $run(
                    "(define ((enum (Foo T) A (B T) C)) (show (((Foo Int) . B) 42)))",
                    ""
                ),
                "(B 42)"
            );

            assert_eq!(
                $run(
                    "(define ((enum (Foo T) A (B T) C)) (show ((Foo . B) 4.2)))",
                    ""
                ),
                "(B 4.2)"
            );

            assert_eq!(
                $run(
                    "(define ((enum (Foo) (B Int))) (show ((Foo . B) 42)))",
                    ""
                ),
                "(B 42)"
            );
        }

        #[test]
        fn enum_destructuring_const() {
            assert_eq!(
                $run("(define ((enum (Foo) A B))
                        (show 
                          (match-enum (Foo . A)
                            (A => 42)
                            (B => 123))))", ""),
                "42"
            );

            assert_eq!(
                $run("(define ((enum (Foo) A B))
                        (show 
                          (match-enum (Foo . B)
                            (A => 42)
                            (B => 123))))", ""),
                "123"
            );
        }

        #[test]
        fn enum_destructuring_binding() {
            assert_eq!(
                $run("(define ((enum (Foo) A (B Int) C))
                        (show 
                          (match-enum ((Foo . B) 951)
                            (A => 42)
                            ((B x) => x)
                            (C => 123))))", ""),
                "951"
            );

            assert_eq!(
                $run("(define ((enum (Foo T) A (B T) C))
                        (show 
                          (match-enum ((Foo . B) 951)
                            (A => 42)
                            ((B x) => x)
                            (C => 123))))", ""),
                "951"
            );

            assert_eq!(
                $run("(define ((enum (Foo T) A (B T) C))
                        (show 
                          (match-enum ((Foo . B) 951)
                            (A => 42)
                            ((B x) => x)
                            (C => 123))))", ""),
                "951"
            );

            assert_eq!(
                $run("(define ((enum (Foo T) A (B T) C))
                        (show 
                          (match-enum ((Foo . B) 3.4)
                            (A => 1.2)
                            ((B x) => x)
                            (C => 5.6))))", ""),
                "3.4"
            );
        }

        #[test]
        fn function_definitions() {
            assert_eq!(
                $run("(define ((func () (foo x : Int -> Int) x))
                        (show (foo 5)))", ""),
                "5"
            );

            assert_eq!(
                $run("(define ((func () (foo x : Int -> ()) (show x)))
                        (show (foo 5)))", ""),
                "5()"
            );

            assert_eq!(
                $run("(define ((func (T) (foo x : T -> T) x))
                        (show (foo \"abc\")))", ""),
                "abc"
            );
        }

        #[test]
        fn recursion() {
            assert_eq!(
                $run("(define (
                               (func () (foo x : Int -> Int) (baz x))
                               (func () (bar y : Int -> Int) y)
                               (func () (baz x : Int -> Int) (bar x)))
                        (show (foo 123)))", ""),
                "123"
            );
        }
    };
}

fn exec(src: &str, input: &str) -> String {
    use crate::{
        languages::{
            mini_lambda::interpreter,
            type_lang::{ast::Expr, type_checker::Checker},
        },
        transformations::{type_lang_monomorphize, type_lang_to_mini_lambda},
    };
    let gs = Arc::new(GensymContext::default());
    let expr_in = Expr::from_str(&src).unwrap();
    let checked = Checker::check_program(&expr_in).unwrap();
    let mono = type_lang_monomorphize::Context::new(gs.clone()).monomporphize(&checked);
    let mini_la = type_lang_to_mini_lambda::Context::new(gs.clone()).convert(&mono);

    let mut o = std::io::Cursor::new(Vec::<u8>::new());
    let mut i = std::io::Cursor::new(input);
    unsafe { interpreter::exec(&mini_la, &mut o, &mut i) }
    String::from_utf8(o.into_inner()).unwrap()
}

make_testsuite_for_type_lang!(exec);
