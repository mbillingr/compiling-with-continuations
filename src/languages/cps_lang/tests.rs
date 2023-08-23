use crate::languages::cps_lang::interpreter::exec;

#[test]
fn test_halt() {
    unsafe {
        assert_eq!(exec(&expr!(halt (int 42))).as_int(), 42);
    }
}
