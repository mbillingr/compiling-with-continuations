macro_rules! value {
    (halt) => {
        $crate::languages::cps_lang::ast::Value::Halt
    };

    (int $x:expr) => {
        $crate::languages::cps_lang::ast::Value::Int($x)
    };

    ($var:ident) => {
        $crate::languages::cps_lang::ast::Value::Var(stringify!($var).into())
    };

    (($($parts:tt)*)) => {
        value!($($parts)*)
    };
}

macro_rules! value_list {
    ($($item:tt)*) => {
        $crate::core::reference::Ref::array(vec![$(value!($item)),*])
    };
}

macro_rules! expr {
    (record [$($values:tt)*] $var:ident $cnt:tt) => {
        $crate::languages::cps_lang::ast::Expr::Record(
            value_list!($($values)*),
            stringify!($var).into(),
            expr!($cnt).into(),
        )
    };

    (select $idx:tt $recval:tt $var:ident $cnt:tt) => {
        $crate::languages::cps_lang::ast::Expr::Select(
            $idx,
            value!($recval),
            stringify!($var).into(),
            expr!($cnt).into(),
        )
    };

    (($($parts:tt)*)) => {
        expr!($($parts)*)
    };

    ($fun:tt $($arg:tt)*) => {
        $crate::languages::cps_lang::ast::Expr::App(
            value!($fun),
            $crate::core::reference::Ref::array(vec![$(value!($arg)),*]))
    };
}
