#[macro_export]
macro_rules! make_testsuite_for_mini_lambda {
    (default_tests $runner:ident) => {
        use $crate::languages::mini_lambda::ast::Expr;

        macro_rules! run {
            ($src:expr) => { $runner(&Expr::from_str($src).unwrap()) };
        }

        #[test]
        fn constants() {
            unsafe {
                assert_eq!(run!("0").as_int(), 0);
                assert_eq!(run!("1.2").as_float(), 1.2);
                assert_eq!(run!("\"abc\"").as_str(), "abc");
            }
        }

        #[test]
        fn record_creation_and_selection() {
            unsafe {
                assert_eq!(run!("(select 0 (record 1 2))").as_int(), 1);
                assert_eq!(run!("(select 1 (record 1 2))").as_int(), 2);
            }
        }

        #[test]
        fn function_definition_and_application() {
            unsafe {
                assert_eq!(run!("((fn x 1) 2)").as_int(), 1);
            }
        }

        #[test]
        fn function_argument_referencing() {
            unsafe {
                assert_eq!(run!("((fn x x) 2)").as_int(), 2);
            }
        }

        #[test]
        fn function_closure_capture() {
            unsafe {
                assert_eq!(run!("(((fn x (fn y x)) 3) 4)").as_int(), 3);
            }
        }

        #[test]
        fn mutual_recursion() {
            unsafe {
                assert_eq!(run!(
                    "(fix ((foo x (bar x))
                           (bar x ((primitive +) (record x 2))))
                       (foo 5))").as_int(),
                    7
                );
                assert_eq!($runner(&mini_expr!(
                    fix fun foo x = (bar x)
                        fun bar x = (- [x (int -2)])
                    in foo (int 5)
                )).as_int(), 7);
            }
        }

        #[test]
        fn primitive_application() {
            unsafe {
                assert_eq!($runner(&mini_expr!(is_zero int 0)).as_int(), 1);
                assert_eq!($runner(&mini_expr!(is_zero int 1)).as_int(), 0);
                assert_eq!($runner(&mini_expr!(is_zero int 2)).as_int(), 0);
                assert_eq!($runner(&mini_expr!(ineg int 1)).as_int(), -1);
                assert_eq!($runner(&mini_expr!(- [(int 1) (int 3)])).as_int(), -2);
                assert_eq!($runner(&mini_expr!(+ [(int 1) (int 2)])).as_int(), 3);
            }
        }

        #[test]
        fn primitive_reification() {
            unsafe {
                assert_eq!(
                    $runner(&mini_expr!(((fun f = fun x = f x) ineg) int 1)).as_int(),
                    -1
                );
                assert_eq!($runner(&mini_expr!(((fun f = fun x = f x) -) [(int 1) (int 3)])).as_int(), -2);
                assert_eq!($runner(&mini_expr!(((fun f = fun x = f x) =) [(int 0) (int 0)])).as_bool(), true);
                assert_eq!($runner(&mini_expr!(((fun f = fun x = f x) =) [(int 2) (int 3)])).as_bool(), false);
            }
        }

        #[test]
        fn switch_over_integers() {
            unsafe {
                assert_eq!($runner(&mini_expr!(switch (int 0) [] [] (int 1))).as_int(), 1); // only the default branch
                assert_eq!(
                    $runner(&mini_expr!(switch (int 0) [] [(int 0) => (int 1)] )).as_int(),
                    1
                );
                assert_eq!(
                    $runner(&mini_expr!(switch (int 0) [] [(int 0) => (int 1); (int 1) => (int 10)] (int -1)))
                        .as_int(),
                    1
                );
                assert_eq!(
                    $runner(&mini_expr!(switch (int 1) [] [(int 0) => (int 1); (int 1) => (int 10)] (int -1)))
                        .as_int(),
                    10
                );
                assert_eq!(
                    $runner(&mini_expr!(switch (int 2) [] [(int 0) => (int 1); (int 1) => (int 10)] (int -1)))
                        .as_int(),
                    -1
                );
            }
        }

        #[test]
        fn switch_over_real() {
            unsafe {
                assert_eq!(
                    $runner(&mini_expr!(switch (real 0.0) [] [] (int 1))).as_int(),
                    1
                ); // only the default branch
                assert_eq!(
                    $runner(&mini_expr!(switch (real 0.0) [] [(real 0.0) => (int 1)] )).as_int(),
                    1
                );
                assert_eq!(
                    $runner(&mini_expr!(switch (real 0.0) [] [(real 0.0) => (int 1); (real 1.0) => (int 10)] (int -1)))
                        .as_int(),
                    1
                );
                assert_eq!(
                    $runner(&mini_expr!(switch (real 1.0) [] [(real 0.0) => (int 1); (real 1.0) => (int 10)] (int -1)))
                        .as_int(),
                    10
                );
                assert_eq!(
                    $runner(&mini_expr!(switch (real 2.0) [] [(real 0.0) => (int 1); (real 1.0) => (int 10)] (int -1)))
                        .as_int(),
                    -1
                );
            }
        }

        #[test]
        fn switch_over_strings() {
            unsafe {
                assert_eq!(
                    $runner(&mini_expr!(switch (str "x") [] [] (int 1))).as_int(),
                    1
                ); // only the default branch
                assert_eq!(
                    $runner(&mini_expr!(switch (str "x") [] [(str "x") => (int 1)] )).as_int(),
                    1
                );
                assert_eq!(
                    $runner(
                        &mini_expr!(switch (str "x") [] [(str "x") => (int 1); (str "y") => (int 10)] (int -1))
                    )
                    .as_int(),
                    1
                );
                assert_eq!(
                    $runner(
                        &mini_expr!(switch (str "y") [] [(str "x") => (int 1); (str "y") => (int 10)] (int -1))
                    )
                    .as_int(),
                    10
                );
                assert_eq!(
                    $runner(
                        &mini_expr!(switch (str "z") [] [(str "x") => (int 1); (str "y") => (int 10)] (int -1))
                    )
                    .as_int(),
                    -1
                );
            }
        }

        #[test]
        fn datatypes() {
            unsafe {
                assert_eq!(
                    $runner(&mini_expr!(decon (tag 42) (con (tag 42) int 7))).as_int(),
                    7
                );

                assert_eq!($runner(&mini_expr!(con (const 42))), Answer::tag(42));

                assert_eq!($runner(&mini_expr!((con transparent int 5))).as_int(), 5);
                assert_eq!($runner(&mini_expr!((decon transparent int 3))).as_int(), 3);
            }
        }

        #[test]
        fn switch_over_datatypes() {
            unsafe {
                assert_eq!(
                    $runner(&mini_expr!(switch (con (tag 0) (int 9)) [] [] (int 1))).as_int(),
                    1
                ); // only the default branch
                assert_eq!($runner(&mini_expr!(switch (con (tag 1) (int 9)) [(tag 0) (tag 1)] [(tag 0) => (int 10)] (int 1))).as_int(), 1);
                assert_eq!($runner(&mini_expr!(switch (con (tag 0) (int 9)) [(tag 0) (tag 1)] [(tag 0) => (int 10)] (int 1))).as_int(), 10);
                assert_eq!($runner(&mini_expr!(switch (con (tag 0) (int 9)) [(tag 0) (const 0)] [(tag 0) => (int 10); (const 0) => (int 100)] (int 1))).as_int(), 10);
                assert_eq!($runner(&mini_expr!(switch (con (const 0)) [(tag 0) (const 0)] [(tag 0) => (int 10); (const 0) => (int 100)] (int 1))).as_int(), 100);
                assert_eq!(
                    $runner(&mini_expr!(switch (con transparent (int 9)) [transparent] [transparent => (int 5)]))
                        .as_int(),
                    5
                );
            }
        }

        #[test]
        fn fibonacci() {
            unsafe {
                let expr = $crate::languages::mini_lambda::ast::Expr::from_str(
                    "(fix ((fib n
                             (switch ((primitive <) (record n 2)) () 
                                     ((1 1) 
                                      (0 ((primitive +) 
                                          (record (fib ((primitive -) (record n 2)))
                                                  (fib ((primitive -) (record n 1)))))))))) 
                        (fib 5))"
                ).unwrap();
                assert_eq!($runner(&expr).as_int(), 8);
            }
        }

    };

    (continuation_tests $runner:ident) => {
        #[test]
        fn callcc_without_capture() {
            unsafe {
                assert_eq!(
                    $runner(&mini_expr!(callcc (fun k = (int 42)))).as_int(),
                    42
                );
            }
        }

        #[test]
        fn callcc_without_explicit_return() {
            unsafe {
                assert_eq!(
                    $runner(&mini_expr!(callcc (fun k = (throw [k (int 42)])))).as_int(),
                    42
                );
            }
        }
    };

    ($runner:ident $($extras:tt)*) => {
        mod mini_lambda_tests {
            use $crate::core::answer::Answer;
            use $crate::mini_expr;
            use super::$runner;

            $crate::make_testsuite_for_mini_lambda!(default_tests $runner);

            $(
                $crate::make_testsuite_for_mini_lambda!($extras $runner);
            )*
        }
    };
}

use crate::languages::mini_lambda::interpreter::exec;
make_testsuite_for_mini_lambda!(exec);
