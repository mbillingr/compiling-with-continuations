use crate::languages::thih_lang::haskell_specific::classes::EnvTransformer;
use crate::languages::thih_lang::haskell_specific::types::{t_double, t_int};
use crate::languages::thih_lang::thih_core::predicates::Pred::IsIn;

pub fn add_core_classes() -> EnvTransformer {
    use EnvTransformer as ET;
    ET::add_class("Eq".into(), vec![])
        .compose(ET::add_class("Ord".into(), vec!["Eq".into()]))
        .compose(ET::add_class("Show".into(), vec![]))
        .compose(ET::add_class("Read".into(), vec![]))
        .compose(ET::add_class("Bounded".into(), vec![]))
        .compose(ET::add_class("Enum".into(), vec![]))
        .compose(ET::add_class("Functor".into(), vec![]))
        .compose(ET::add_class("Monad".into(), vec![]))
}

pub fn add_num_classes() -> EnvTransformer {
    use EnvTransformer as ET;
    let et = ET::add_class("Num".into(), vec!["Eq".into(), "Show".into()])
        .compose(ET::add_class(
            "Real".into(),
            vec!["Num".into(), "Ord".into()],
        ))
        .compose(ET::add_class("Fractional".into(), vec!["Num".into()]))
        .compose(ET::add_class(
            "Integral".into(),
            vec!["Real".into(), "Enum".into()],
        ))
        .compose(ET::add_class(
            "RealFrac".into(),
            vec!["Real".into(), "Fractional".into()],
        ))
        .compose(ET::add_class("Floating".into(), vec!["Fractional".into()]))
        .compose(ET::add_class(
            "RealFloat".into(),
            vec!["RealFrac".into(), "Floating".into()],
        ));

    et.compose(ET::add_inst(vec![], IsIn("Num".into(), t_int())))
        .compose(ET::add_inst(vec![], IsIn("Show".into(), t_int())))
        .compose(ET::add_inst(vec![], IsIn("Num".into(), t_double())))
}
