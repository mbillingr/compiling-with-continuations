macro_rules! value {
    (halt) => {
        $crate::languages::cps_lang::ast::Value::Halt
    };

    (int $x:expr) => {
        $crate::languages::cps_lang::ast::Value::Int($x)
    };

    (($($parts:tt)*)) => {
        value!($($parts)*)
    };
}

macro_rules! expr {
    ($fun:tt $($arg:tt)*) => {
        $crate::languages::cps_lang::ast::Expr::App(
            value!($fun),
            $crate::core::reference::Ref::array(vec![$(value!($arg)),*]))
    };
}
