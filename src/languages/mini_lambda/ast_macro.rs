macro_rules! expr {

    (int $x:expr) => { $crate::languages::mini_lambda::ast::Expr::Int($x) };

    (fun $v:ident = $($bdy:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::Fn(stringify!($v).into(), expr!($($bdy)+).into())
    };

    ([$($x:tt)*]) => { $crate::languages::mini_lambda::ast::Expr::Record($crate::core::reference::Ref::array(vec![$(expr!($x)),*])) };

    (select $rec:tt $idx:expr) => {
        $crate::languages::mini_lambda::ast::Expr::Select($idx, expr!($rec).into())
    };

    (switch $x:tt $possible_conreps:tt $branches:tt) => {
        expr!(@switch_raw $x $possible_conreps $branches None)
    };

    (switch $x:tt $possible_conreps:tt $branches:tt $default:tt) => {
        expr!(@switch_raw $x $possible_conreps $branches Some(expr!($default).into()))
    };

    (@switch_raw $x:tt [$($possible_conreps:path)*] $branches:tt $default:expr) => {
        $crate::languages::mini_lambda::ast::Expr::Switch(
            expr!($x).into(),
            $crate::core::reference::Ref::array(vec![$($possible_conreps)*]),
            $crate::core::reference::Ref::array(expr!(@switch_branches $branches)),
            $default)
    };

    (@switch_branches [$((int $val:expr) => $body:tt)*]) => {
        vec![$(($crate::languages::mini_lambda::ast::Con::Int($val), expr!($body))),*]
    };

    (con (tag $t:expr) $($v:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::Con(
            $crate::languages::mini_lambda::ast::ConRep::Tagged($t),
            expr!($($v)+).into()
        )
    };

    (decon (tag $t:expr) $($v:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::DeCon(
            $crate::languages::mini_lambda::ast::ConRep::Tagged($t),
            expr!($($v)+).into()
        )
    };

    (con transparent $($v:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::Con(
            $crate::languages::mini_lambda::ast::ConRep::Transparent,
            expr!($($v)+).into()
        )
    };

    (decon transparent $($v:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::DeCon(
            $crate::languages::mini_lambda::ast::ConRep::Transparent,
            expr!($($v)+).into()
        )
    };

    ($rator:tt $($rand:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::App(expr!($rator).into(), expr!($($rand)+).into())
    };

    (($($x:tt)+)) => { expr!($($x)+) };

    (ineg) => {
        $crate::languages::mini_lambda::ast::Expr::Prim($crate::languages::mini_lambda::ast::PrimOp::INeg)
    };

    (isub) => {
        $crate::languages::mini_lambda::ast::Expr::Prim($crate::languages::mini_lambda::ast::PrimOp::ISub)
    };

    ($var:ident) => { $crate::languages::mini_lambda::ast::Expr::Var(stringify!($var).into()) };
}
