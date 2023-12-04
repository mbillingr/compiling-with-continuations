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

            assert_eq!(
                $run(
                    "(define ((enum (Foo) (B Int Int Int))) (show ((Foo . B) 1 2 3)))",
                    ""
                ),
                "(B 1 2 3)"
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
                $run("(define ((func () (foo (x : Int) -> Int) x))
                        (show (foo 5)))", ""),
                "5"
            );

            assert_eq!(
                $run("(define ((func () (foo (x : Int) -> ()) (show x)))
                        (show (foo 5)))", ""),
                "5()"
            );

            assert_eq!(
                $run("(define ((func () (foo (x : Int) -> Int) (begin (show x) 2)))
                        (show (foo 4)))", ""),
                "42"
            );

            assert_eq!(
                $run("(define ((func (T) (foo (x : T) -> T) x))
                        (show (foo \"abc\")))", ""),
                "abc"
            );
            assert_eq!(
                $run("(define ((func () (foo (x : Int) (y : Int) (z : Int) -> Int) y))
                        (show (foo 1 2 3)))", ""),
                "2"
            );
        }

        #[test]
        fn records() {
            assert_eq!(
                $run("(show (record 1 2 3))", ""),
                "[1 2 3]");

            assert_eq!(
                $run("(show (select 1 (record 1 2 3)))", ""),
                "2");

            assert_eq!(
                $run("(define ((func (A B) (swap (r : (Record A B)) -> (Record B A))
                                 (record (select 1 r) (select 0 r))
                               )
                              )
                        (show (swap (record 1 \"x\"))))", ""),
                "[x 1]");
        }

        #[test]
        fn recursion() {
            assert_eq!(
                $run("(define ((func () (foo (x : Int) -> Int) (baz x))
                               (func () (bar (y : Int) -> Int) y)
                               (func () (baz (x : Int) -> Int) (bar x)))
                        (show (foo 123)))", ""),
                "123"
            );

            assert_eq!(
                $run("(define ((enum (Recur) Yes No)
                               (func () (foo (x : Recur) -> Int)
                                 (match-enum x
                                   (No => 1)
                                   (Yes => (foo (Recur . No))))))
                        (show (foo (Recur . Yes))))", ""),
                "1"
            );

            // recursive function on recursive data type
            assert_eq!(
                $run("(define ((enum (Peano) Z (S Peano))
                               (func (T) (z (_ : T) -> Peano) (Peano . Z))
                               (func (T) (s (n : Peano) -> Peano) ((Peano . S) n))
                               (func () (peano->int (n : Peano) -> Int)
                                 (match-enum n
                                   (Z => 0)
                                   ((S k) => (+ 1 (peano->int k))))))
                        (show 
                          (peano->int 
                            (s (s (s (z 0)))))))", ""),
                "3"
            );
        }

        #[test]
        fn a_list_implementation() {
            assert_eq!(
                $run("(define ((enum (List T) Nil (Cons (Record T (List T))))
                               (func (T) (nil (_ : T) -> (List T)) (List . Nil))
                               (func (T) (cons (x : (Record T (List T))) -> (List T)) ((List . Cons) x))
                               (func (T) (car (xs : (List T)) -> T)
                                 (match-enum xs
                                   ((Cons r) => (select 0 r))))
                               (func (T) (cdr (xs : (List T)) -> (List T))
                                 (match-enum xs
                                   ((Cons r) => (select 1 r))))
                              )
                        (show (car (cons (record 42 (nil 0))))))", ""),
                "42"
            );
        }

        #[test]
        fn escaping_type() {
            assert_eq!(
                $run("(show (define ((enum (Foo) A B)) (Foo . A)))", ""),
                "A"
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
