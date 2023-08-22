macro_rules! expr {

    (int $x:expr) => { $crate::languages::mini_lambda::ast::Expr::Int($x) };

    (real $x:expr) => { $crate::languages::mini_lambda::ast::Expr::Real($x) };

    (str $x:expr) => { $crate::languages::mini_lambda::ast::Expr::String($x.to_string().into()) };

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

    (@switch_raw $x:tt [$($possible_conreps:tt)*] $branches:tt $default:expr) => {
        $crate::languages::mini_lambda::ast::Expr::Switch(
            expr!($x).into(),
            $crate::core::reference::Ref::array(vec![$(expr!(@conrep $possible_conreps)),*]),
            $crate::core::reference::Ref::array(expr!(@switch_branches $branches)),
            $default)
    };

    (@conrep (tag $t:expr)) => {
        $crate::languages::mini_lambda::ast::ConRep::Tagged($t)
    };

    (@conrep (const $t:expr)) => {
        $crate::languages::mini_lambda::ast::ConRep::Constant($t)
    };

    (@conrep transparent) => {
        $crate::languages::mini_lambda::ast::ConRep::Transparent
    };

    (@concase (int $val:expr)) => {
        $crate::languages::mini_lambda::ast::Con::Int($val)
    };

    (@concase (real $val:expr)) => {
        $crate::languages::mini_lambda::ast::Con::Real($val)
    };

    (@concase (str $val:expr)) => {
        $crate::languages::mini_lambda::ast::Con::String($val.into())
    };

    (@concase $conrep:tt) => {
        $crate::languages::mini_lambda::ast::Con::Data(expr!(@conrep $conrep))
    };

    (@switch_branches [$($concase:tt => $body:tt);*]) => {
        vec![
            $((
                expr!(@concase $concase),
                expr!($body)
            )),*
            ]
    };

    (con (const $t:expr)) => {
        $crate::languages::mini_lambda::ast::Expr::Con(
            $crate::languages::mini_lambda::ast::ConRep::Constant($t),
            $crate::languages::mini_lambda::ast::Expr::Int(0).into()
        )
    };

    (con $conrep:tt $($v:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::Con(
            expr!(@conrep $conrep),
            expr!($($v)+).into()
        )
    };

    (decon $conrep:tt $($v:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::DeCon(
            expr!(@conrep $conrep),
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
