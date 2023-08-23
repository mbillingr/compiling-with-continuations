use crate::core::answer::Answer;
use crate::core::env::Env;
use crate::languages::cps_lang::interpreter::{eval_expr, exec};

#[test]
fn test_halt() {
    unsafe {
        assert_eq!(exec(&expr!(halt (int 42))).as_int(), 42);
    }
}

#[test]
fn test_record() {
    unsafe {
        let rec = exec(&expr!(record [(int 1) (int 20) (int 300)] r (halt r)));
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
            eval_expr(&expr!(select 0 rec out (halt out)), env).as_int(),
            11
        );
        assert_eq!(
            eval_expr(&expr!(select 1 rec out (halt out)), env).as_int(),
            33
        );
    }
}

#[test]
fn test_functions() {
    unsafe {
        assert_eq!(exec(&expr!(fix in (halt (int 0)))).as_int(), 0);
        assert_eq!(
            exec(&expr!(fix foo(c)=(c (int 42)) in (foo halt))).as_int(),
            42
        );
    }
}
