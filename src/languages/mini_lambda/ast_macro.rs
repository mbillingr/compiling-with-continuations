macro_rules! expr {
    (($($x:tt)+)) => { expr!($($x)+) };

    (int $x:expr) => { $crate::languages::mini_lambda::ast::Expr::Int($x) };

    (fun $v:ident = $($bdy:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::Fn(stringify!($v).into(), expr!($($bdy)+).into())
    };

    ($rator:tt $($rand:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::App(expr!($rator).into(), expr!($($rand)+).into())
    };

    ($var:ident) => { $crate::languages::mini_lambda::ast::Expr::Var(stringify!($var).into()) };
}
