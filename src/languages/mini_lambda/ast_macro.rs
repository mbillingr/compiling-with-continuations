#[macro_export]
macro_rules! mini_expr {

    (int $x:expr) => { $crate::languages::mini_lambda::ast::Expr::Int($x) };

    (real $x:expr) => { $crate::languages::mini_lambda::ast::Expr::Real($x) };

    (str $x:expr) => { $crate::languages::mini_lambda::ast::Expr::String($x.to_string().into()) };

    (fun $v:ident = $($bdy:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::Fn(stringify!($v).into(), mini_expr!($($bdy)+).into())
    };

    (fix $(fun $fname:ident $farg:ident = $fbody:tt)* in $($body:tt)+ ) => {
        $crate::languages::mini_lambda::ast::Expr::Fix(
            $crate::core::reference::Ref::array(vec![$(stringify!($fname).into()),*]),
            $crate::core::reference::Ref::array(vec![$(
                mini_expr!(fun $farg = $fbody)
            ),*]),
            mini_expr!($($body)+).into()
        )
    };

    ([$($x:tt)*]) => { $crate::languages::mini_lambda::ast::Expr::Record($crate::core::reference::Ref::array(vec![$(mini_expr!($x)),*])) };

    (select $rec:tt $idx:expr) => {
        $crate::languages::mini_lambda::ast::Expr::Select($idx, mini_expr!($rec).into())
    };

    (switch $x:tt $possible_conreps:tt $branches:tt) => {
        mini_expr!(@switch_raw $x $possible_conreps $branches None)
    };

    (switch $x:tt $possible_conreps:tt $branches:tt $default:tt) => {
        mini_expr!(@switch_raw $x $possible_conreps $branches Some(mini_expr!($default).into()))
    };

    (@switch_raw $x:tt [$($possible_conreps:tt)*] $branches:tt $default:expr) => {
        $crate::languages::mini_lambda::ast::Expr::Switch(
            mini_expr!($x).into(),
            $crate::core::reference::Ref::array(vec![$(mini_expr!(@conrep $possible_conreps)),*]),
            $crate::core::reference::Ref::array(mini_expr!(@switch_branches $branches)),
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
        $crate::languages::mini_lambda::ast::Con::Data(mini_expr!(@conrep $conrep))
    };

    (@switch_branches [$($concase:tt => $body:tt);*]) => {
        vec![
            $((
                mini_expr!(@concase $concase),
                mini_expr!($body)
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
            mini_expr!(@conrep $conrep),
            mini_expr!($($v)+).into()
        )
    };

    (decon $conrep:tt $($v:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::DeCon(
            mini_expr!(@conrep $conrep),
            mini_expr!($($v)+).into()
        )
    };

    ($rator:tt $($rand:tt)+) => {
        $crate::languages::mini_lambda::ast::Expr::App(mini_expr!($rator).into(), mini_expr!($($rand)+).into())
    };

    (($($x:tt)+)) => { mini_expr!($($x)+) };

    (ineg) => {
        $crate::languages::mini_lambda::ast::Expr::Prim(
            $crate::languages::common_primops::PrimOp::INeg)
    };

    (-) => {
        $crate::languages::mini_lambda::ast::Expr::Prim(
            $crate::languages::common_primops::PrimOp::ISub)
    };

    (+) => {
        $crate::languages::mini_lambda::ast::Expr::Prim(
            $crate::languages::common_primops::PrimOp::IAdd)
    };

    ($var:ident) => { $crate::languages::mini_lambda::ast::Expr::Var(stringify!($var).into()) };
}
