macro_rules! expr {
    (int $x:expr) => { $crate::languages::mini_lambda::ast::Expr::Int($x) };

    (fun $v:ident = $($bdy:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::Fn(stringify!($v).into(), expr!($($bdy)+).into())
    };

    ([$($x:tt)*]) => { $crate::languages::mini_lambda::ast::Expr::Record($crate::core::reference::Ref::tuple(vec![$(expr!($x)),*])) };

    (select $rec:tt $idx:expr) => {
        $crate::languages::mini_lambda::ast::Expr::Select($idx, expr!($rec).into())
    };

    ($rator:tt $($rand:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::App(expr!($rator).into(), expr!($($rand)+).into())
    };

    (($($x:tt)+)) => { expr!($($x)+) };

    (neg) => {
        $crate::languages::mini_lambda::ast::Expr::Prim($crate::languages::mini_lambda::ast::PrimOp::Neg)
    };

    ($var:ident) => { $crate::languages::mini_lambda::ast::Expr::Var(stringify!($var).into()) };
}
