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

macro_rules! ident_list {
    ($($item:ident)*) => {
        $crate::core::reference::Ref::array(vec![$(stringify!($item).into()),*])
    };
}

macro_rules! expr_list {
    ($($item:tt)*) => {
        $crate::core::reference::Ref::array(vec![$(expr!($item).into()),*])
    };
}

macro_rules! expr {

    (($($parts:tt)*)) => {
        expr!($($parts)*)
    };

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

    (fix in $cnt:tt) => {
        expr!($cnt)
    };

    (fix $($name:ident($($arg:ident)*)=$body:tt);+ in $cnt:tt) => {
        $crate::languages::cps_lang::ast::Expr::Fix(
            $crate::core::reference::Ref::array(vec![$((
                stringify!($name).into(),
                ident_list!($($arg)*),
                expr!($body).into()
            )),*]),
            expr!($cnt).into()
        )
    };

    (switch $val:tt [$($cnt:tt)*]) => {
        $crate::languages::cps_lang::ast::Expr::Switch(
            value!($val),
            expr_list!($($cnt)*),
        )
    };

    (- [$($values:tt)*] [$($var:ident)*] [$($cnt:tt)*]) => {
        $crate::languages::cps_lang::ast::Expr::PrimOp(
            $crate::languages::cps_lang::ast::PrimOp::ISub,
            value_list!($($values)*),
            ident_list!($($var)*),
            expr_list!($($cnt)*),
        )
    };

    ($fun:tt $($arg:tt)*) => {
        $crate::languages::cps_lang::ast::Expr::App(
            value!($fun),
            $crate::core::reference::Ref::array(vec![$(value!($arg)),*]))
    };
}
