#[macro_export]
macro_rules! cps_value {
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
        cps_value!($($parts)*)
    };
}

macro_rules! cps_value_list {
    ($($item:tt)*) => {
        $crate::core::reference::Ref::array(vec![$(cps_value!($item)),*])
    };
}

macro_rules! cps_ident_list {
    ($($item:ident)*) => {
        $crate::core::reference::Ref::array(vec![$(stringify!($item).into()),*])
    };
}

macro_rules! cps_expr_list {
    ($($item:tt)*) => {
        $crate::core::reference::Ref::array(vec![$(cps_expr!($item).into()),*])
    };
}

#[macro_export]
macro_rules! cps_expr {

    (($($parts:tt)*)) => {
        cps_expr!($($parts)*)
    };

    (record [$($values:tt)*] $var:ident $cnt:tt) => {
        $crate::languages::cps_lang::ast::Expr::Record(
            cps_value_list!($($values)*),
            stringify!($var).into(),
            cps_expr!($cnt).into(),
        )
    };

    (select $idx:tt $recval:tt $var:ident $cnt:tt) => {
        $crate::languages::cps_lang::ast::Expr::Select(
            $idx,
            cps_value!($recval),
            stringify!($var).into(),
            cps_expr!($cnt).into(),
        )
    };

    (offset $idx:tt $recval:tt $var:ident $cnt:tt) => {
        $crate::languages::cps_lang::ast::Expr::Offset(
            $idx,
            cps_value!($recval),
            stringify!($var).into(),
            cps_expr!($cnt).into(),
        )
    };

    (fix in $cnt:tt) => {
        cps_expr!($cnt)
    };

    (fix $($name:ident($($arg:ident)*)=$body:tt);+ in $cnt:tt) => {
        $crate::languages::cps_lang::ast::Expr::Fix(
            $crate::core::reference::Ref::array(vec![$((
                stringify!($name).into(),
                cps_ident_list!($($arg)*),
                cps_expr!($body).into()
            )),*]),
            cps_expr!($cnt).into()
        )
    };

    (switch $val:tt [$($cnt:tt)*]) => {
        $crate::languages::cps_lang::ast::Expr::Switch(
            cps_value!($val),
            cps_expr_list!($($cnt)*),
        )
    };

    (- [$($values:tt)*] [$($var:ident)*] [$($cnt:tt)*]) => {
        $crate::languages::cps_lang::ast::Expr::PrimOp(
            $crate::languages::cps_lang::ast::PrimOp::ISub,
            cps_value_list!($($values)*),
            cps_ident_list!($($var)*),
            cps_expr_list!($($cnt)*),
        )
    };

    ($fun:tt $($arg:tt)*) => {
        $crate::languages::cps_lang::ast::Expr::App(
            cps_value!($fun),
            $crate::core::reference::Ref::array(vec![$(cps_value!($arg)),*]))
    };
}
