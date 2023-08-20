use crate::languages::mini_lambda::interpreter::exec;

#[test]
fn constants() {
    unsafe {
        assert_eq!(exec(&expr!(int 0)).as_int(), 0);
    }
}

#[test]
fn function_records() {
    unsafe {
        assert_eq!(exec(&expr!(select [(int 1) (int 2)] 0)).as_int(), 1);
        assert_eq!(exec(&expr!(select [(int 1) (int 2)] 1)).as_int(), 2);
    }
}

#[test]
fn function_definition_and_application() {
    unsafe {
        assert_eq!(exec(&expr!((fun x = int 1) int 2)).as_int(), 1);
    }
}

#[test]
fn function_argument_referencing() {
    unsafe {
        assert_eq!(exec(&expr!((fun x = x) int 2)).as_int(), 2);
    }
}

#[test]
fn function_closure_capture() {
    unsafe {
        assert_eq!(exec(&expr!(((fun x = fun y = x) int 3) int 4)).as_int(), 3);
    }
}
