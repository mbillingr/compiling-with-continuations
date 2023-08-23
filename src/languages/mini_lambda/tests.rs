use crate::core::answer::Answer;
use crate::languages::mini_lambda::interpreter::exec;

#[test]
fn constants() {
    unsafe {
        assert_eq!(exec(&mini_expr!(int 0)).as_int(), 0);
        assert_eq!(exec(&mini_expr!(real 1.2)).as_float(), 1.2);
        assert_eq!(exec(&mini_expr!(str "abc")).as_str(), "abc");
    }
}

#[test]
fn record_creation_and_selection() {
    unsafe {
        assert_eq!(exec(&mini_expr!(select [(int 1) (int 2)] 0)).as_int(), 1);
        assert_eq!(exec(&mini_expr!(select [(int 1) (int 2)] 1)).as_int(), 2);
    }
}

#[test]
fn function_definition_and_application() {
    unsafe {
        assert_eq!(exec(&mini_expr!((fun x = int 1) int 2)).as_int(), 1);
    }
}

#[test]
fn function_argument_referencing() {
    unsafe {
        assert_eq!(exec(&mini_expr!((fun x = x) int 2)).as_int(), 2);
    }
}

#[test]
fn function_closure_capture() {
    unsafe {
        assert_eq!(
            exec(&mini_expr!(((fun x = fun y = x) int 3) int 4)).as_int(),
            3
        );
    }
}

#[test]
fn mutual_recursion() {
    unsafe {
        assert_eq!(exec(&mini_expr!(
            fix fun foo x = (bar x)
                fun bar x = (isub [x (int -2)])
            in foo (int 5)
        )).as_int(), 7);
    }
}

#[test]
fn primitive_application() {
    unsafe {
        assert_eq!(exec(&mini_expr!(ineg int 1)).as_int(), -1);
        assert_eq!(exec(&mini_expr!(isub [(int 1) (int 3)])).as_int(), -2);
    }
}

#[test]
fn primitive_reification() {
    unsafe {
        assert_eq!(
            exec(&mini_expr!(((fun f = fun x = f x) ineg) int 1)).as_int(),
            -1
        );
        assert_eq!(exec(&mini_expr!(((fun f = fun x = f x) isub) [(int 1) (int 3)])).as_int(), -2);
    }
}

#[test]
fn switch_over_integers() {
    unsafe {
        assert_eq!(exec(&mini_expr!(switch (int 0) [] [] (int 1))).as_int(), 1); // only the default branch
        assert_eq!(
            exec(&mini_expr!(switch (int 0) [] [(int 0) => (int 1)] )).as_int(),
            1
        );
        assert_eq!(
            exec(&mini_expr!(switch (int 0) [] [(int 0) => (int 1); (int 1) => (int 10)] (int -1)))
                .as_int(),
            1
        );
        assert_eq!(
            exec(&mini_expr!(switch (int 1) [] [(int 0) => (int 1); (int 1) => (int 10)] (int -1)))
                .as_int(),
            10
        );
        assert_eq!(
            exec(&mini_expr!(switch (int 2) [] [(int 0) => (int 1); (int 1) => (int 10)] (int -1)))
                .as_int(),
            -1
        );
    }
}

#[test]
fn switch_over_real() {
    unsafe {
        assert_eq!(
            exec(&mini_expr!(switch (real 0.0) [] [] (int 1))).as_int(),
            1
        ); // only the default branch
        assert_eq!(
            exec(&mini_expr!(switch (real 0.0) [] [(real 0.0) => (int 1)] )).as_int(),
            1
        );
        assert_eq!(
            exec(&mini_expr!(switch (real 0.0) [] [(real 0.0) => (int 1); (real 1.0) => (int 10)] (int -1)))
                .as_int(),
            1
        );
        assert_eq!(
            exec(&mini_expr!(switch (real 1.0) [] [(real 0.0) => (int 1); (real 1.0) => (int 10)] (int -1)))
                .as_int(),
            10
        );
        assert_eq!(
            exec(&mini_expr!(switch (real 2.0) [] [(real 0.0) => (int 1); (real 1.0) => (int 10)] (int -1)))
                .as_int(),
            -1
        );
    }
}

#[test]
fn switch_over_strings() {
    unsafe {
        assert_eq!(
            exec(&mini_expr!(switch (str "x") [] [] (int 1))).as_int(),
            1
        ); // only the default branch
        assert_eq!(
            exec(&mini_expr!(switch (str "x") [] [(str "x") => (int 1)] )).as_int(),
            1
        );
        assert_eq!(
            exec(
                &mini_expr!(switch (str "x") [] [(str "x") => (int 1); (str "y") => (int 10)] (int -1))
            )
            .as_int(),
            1
        );
        assert_eq!(
            exec(
                &mini_expr!(switch (str "y") [] [(str "x") => (int 1); (str "y") => (int 10)] (int -1))
            )
            .as_int(),
            10
        );
        assert_eq!(
            exec(
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
            exec(&mini_expr!(decon (tag 42) (con (tag 42) int 7))).as_int(),
            7
        );

        assert_eq!(exec(&mini_expr!(con (const 42))), Answer::tag(42));

        assert_eq!(exec(&mini_expr!((con transparent int 5))).as_int(), 5);
        assert_eq!(exec(&mini_expr!((decon transparent int 3))).as_int(), 3);
    }
}

#[test]
fn switch_over_datatypes() {
    unsafe {
        assert_eq!(
            exec(&mini_expr!(switch (con (tag 0) (int 9)) [] [] (int 1))).as_int(),
            1
        ); // only the default branch
        assert_eq!(exec(&mini_expr!(switch (con (tag 1) (int 9)) [(tag 0) (tag 1)] [(tag 0) => (int 10)] (int 1))).as_int(), 1);
        assert_eq!(exec(&mini_expr!(switch (con (tag 0) (int 9)) [(tag 0) (tag 1)] [(tag 0) => (int 10)] (int 1))).as_int(), 10);
        assert_eq!(exec(&mini_expr!(switch (con (tag 0) (int 9)) [(tag 0) (const 0)] [(tag 0) => (int 10); (const 0) => (int 100)] (int 1))).as_int(), 10);
        assert_eq!(exec(&mini_expr!(switch (con (const 0)) [(tag 0) (const 0)] [(tag 0) => (int 10); (const 0) => (int 100)] (int 1))).as_int(), 100);
        assert_eq!(
            exec(&mini_expr!(switch (con transparent (int 9)) [transparent] [transparent => (int 5)]))
                .as_int(),
            5
        );
    }
}
