use crate::languages::cps_lang::interpreter::exec;

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
