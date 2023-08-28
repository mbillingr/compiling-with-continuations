use crate::core::answer::Answer;
use crate::core::env::Env;
use crate::languages::cps_lang::interpreter::{eval_expr, exec};

#[test]
fn test_halt() {
    unsafe {
        assert_eq!(exec(&cps_expr!(halt (int 42))).as_int(), 42);
        assert_eq!(exec(&cps_expr!(halt (real 4.2))).as_float(), 4.2);
    }
}

#[test]
fn test_record() {
    unsafe {
        let rec = exec(&cps_expr!(record [(int 1) (int 20) (int 300)] r (halt r)));
        assert_eq!(rec.get_item(0).as_int(), 1);
        assert_eq!(rec.get_item(1).as_int(), 20);
        assert_eq!(rec.get_item(2).as_int(), 300);
    }
}

#[test]
fn test_select() {
    unsafe {
        let env = Env::Empty.extend(
            "rec".into(),
            Answer::tuple(vec![Answer::from_int(11), Answer::from_int(33)]),
        );
        assert_eq!(
            eval_expr(&cps_expr!(select 0 rec out (halt out)), env).as_int(),
            11
        );
        assert_eq!(
            eval_expr(&cps_expr!(select 1 rec out (halt out)), env).as_int(),
            33
        );
    }
}

#[test]
fn test_offset() {
    unsafe {
        let env = Env::Empty.extend(
            "rec".into(),
            Answer::tuple(vec![
                Answer::from_int(11),
                Answer::from_int(22),
                Answer::from_int(33),
            ]),
        );
        assert_eq!(
            eval_expr(
                &cps_expr!(offset 2 rec sub (select 0 sub out (halt out))),
                env
            )
            .as_int(),
            33
        );
        assert_eq!(
            eval_expr(
                &cps_expr!(offset 2 rec sub (offset (-1) sub sub (select 0 sub out (halt out)))),
                env
            )
            .as_int(),
            22
        );
    }
}

#[test]
fn test_functions() {
    unsafe {
        assert_eq!(exec(&cps_expr!(fix in (halt (int 0)))).as_int(), 0);
        assert_eq!(
            exec(&cps_expr!(fix foo(c)=(c (int 42)) in (foo halt))).as_int(),
            42
        );
    }
}

#[test]
fn test_mutual_recursion() {
    unsafe {
        assert_eq!(
            exec(&cps_expr!(fix foo(c)=(bar (int 42) c); bar(x c)=(c x) in (foo halt))).as_int(),
            42
        );
    }
}

#[test]
fn test_switch() {
    unsafe {
        assert_eq!(
            exec(&cps_expr!(switch (int 0) [(halt (int 11)) (halt (int 22)) (halt (int 33))]))
                .as_int(),
            11
        );
        assert_eq!(
            exec(&cps_expr!(switch (int 1) [(halt (int 11)) (halt (int 22)) (halt (int 33))]))
                .as_int(),
            22
        );
        assert_eq!(
            exec(&cps_expr!(switch (int 2) [(halt (int 11)) (halt (int 22)) (halt (int 33))]))
                .as_int(),
            33
        );
    }
}

#[test]
fn test_primops() {
    unsafe {
        assert_eq!(exec(&cps_expr!(- (int 2) [r] [(halt r)])).as_int(), -2);
        assert_eq!(
            exec(&cps_expr!(- [(int 7) (int 2)] [r] [(halt r)])).as_int(),
            5
        );
        assert_eq!(
            exec(&cps_expr!(+ [(int 7) (int 2)] [r] [(halt r)])).as_int(),
            9
        );
    }
}