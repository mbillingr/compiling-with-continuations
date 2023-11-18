use crate::transformations::GensymContext;
use std::sync::Arc;
macro_rules! make_testsuite_for_type_lang {
    ($run:path) => {
        #[test]
        fn constants() {
            assert_eq!($run("(show 42)", ""), "42");
            assert_eq!($run("(show 12.34)", ""), "12.34");
            assert_eq!($run("(show \"äöü\")", ""), "äöü");
        }

        #[test]
        fn enums() {
            assert_eq!(
                $run("(define ((enum (Foo) A B)) (show (Foo . A)))", ""),
                "A"
            );

            assert_eq!(
                $run(
                    "(define ((enum (Foo) A (B Int) C)) (show ((Foo . B) 42)))",
                    ""
                ),
                "(B ...)"
            );
            assert_eq!(
                $run("(define ((enum (Foo T) A B)) (show ((Foo Int) . A)))", ""),
                "A"
            );

            assert_eq!(
                $run(
                    "(define ((enum (Foo T) A (B T) C)) (show (((Foo Int) . B) 42)))",
                    ""
                ),
                "(B ...)"
            );
        }
    };
}

// (Foo . A)
// ((Foo . B) 42)
// ((Option Int) . None)
// (((Option Int) . Some) 42)
// (Option . None)
// ((Option Some) 42)

fn exec(src: &str, input: &str) -> String {
    use crate::{
        languages::{
            mini_lambda::interpreter,
            type_lang::{ast::Expr, type_checker::Checker},
        },
        transformations::{type_lang_monomorphize, type_lang_to_mini_lambda},
    };
    let gs = Arc::new(GensymContext::default());
    let expr_in = Expr::from_str(&src).unwrap();
    let checked = Checker::check_program(&expr_in).unwrap();
    let mono = type_lang_monomorphize::Context::new(gs.clone()).monomporphize(&checked);
    let mini_la = type_lang_to_mini_lambda::Context::new(gs.clone()).convert(&mono);

    let mut o = std::io::Cursor::new(Vec::<u8>::new());
    let mut i = std::io::Cursor::new(input);
    unsafe { interpreter::exec(&mini_la, &mut o, &mut i) }
    String::from_utf8(o.into_inner()).unwrap()
}

make_testsuite_for_type_lang!(exec);
