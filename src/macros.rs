//! Mikino's macros.

/// Imports mikino's prelude.
#[macro_export]
macro_rules! prelude {
    {} => { use $crate::prelude::*; };
    { pub } => { pub use $crate::prelude::*; };
}

/// Convenience macro, provides a DSL for writing expressions.
///
/// - identifiers must be written as `(var_name: var_typ)`, without any quotes.
#[macro_export]
macro_rules! build_expr {
    (true) => ( $crate::expr::PExpr::from(true) );
    (false) => ( $crate::expr::PExpr::from(false) );

    ( ($var:ident : $typ:ident) ) => (
        $crate::expr::PExpr::new_var(
            $crate::expr::Var::new(stringify!($var), $crate::build_typ!($typ))
        )
    );
    ( ($var:ident @ 0 : $typ:ident) ) => (
        $crate::expr::PExpr::new_var(
            $crate::expr::SVar::new_curr(
                $crate::expr::Var::new(stringify!($var), $crate::build_typ!($typ))
            )
        )
    );
    ( ($var:ident @ 1 : $typ:ident) ) => (
        $crate::expr::PExpr::new_var(
            $crate::expr::SVar::new_next(
                $crate::expr::Var::new(stringify!($var), $crate::build_typ!($typ))
            )
        )
    );

    ( ($op:tt $($args:tt)*) ) => (
        $crate::expr::PExpr::from((
            $crate::build_expr!(@op $op),
            vec![ $($crate::build_expr!($args)),* ],

        ))
    );

    ($cst:expr) => ( $crate::expr::PExpr::from($cst) );

    (@op ite) => ( $crate::expr::Op::Ite );
    (@op +) => ( $crate::expr::Op::Add );
    (@op -) => ( $crate::expr::Op::Sub );
    (@op *) => ( $crate::expr::Op::Mul );
    (@op /) => ( $crate::expr::Op::Div );
    (@op %) => ( $crate::expr::Op::Mod );
    (@op >=) => ( $crate::expr::Op::Ge );
    (@op <=) => ( $crate::expr::Op::Le );
    (@op >) => ( $crate::expr::Op::Gt );
    (@op <) => ( $crate::expr::Op::Lt );
    (@op =) => ( $crate::expr::Op::Eq );
    (@op not) => ( $crate::expr::Op::Not );
    (@op and) => ( $crate::expr::Op::And );
    (@op or) => ( $crate::expr::Op::Or );
    (@op !) => ( $crate::expr::Op::Not );
    (@op &&) => ( $crate::expr::Op::And );
    (@op ||) => ( $crate::expr::Op::Or );
}

/// Builds a type.
#[macro_export]
macro_rules! build_typ {
    (bool) => {
        $crate::expr::Typ::Bool
    };
    (int) => {
        $crate::expr::Typ::Int
    };
    (rat) => {
        $crate::expr::Typ::Rat
    };
}

/// Builds some declarations.
#[macro_export]
macro_rules! build_decls {
    {
        $( $($ident:ident),* $(,)* : $typ:tt )*
    } => {{
        let mut decls: $crate::prelude::Res<$crate::trans::Decls> = Ok($crate::trans::Decls::new());
        $(
            decls = decls.and_then(|mut decls| {
                $(
                    let prev = decls.register(stringify!($ident), $crate::build_typ!($typ));
                    if prev.is_some() {
                        bail!("found multiple definitions of identifier `{}`", stringify!($ident))
                    }
                )*
                Ok(decls)
            });
        )*
        decls
    }};
}

// /// Builds some variable declarations.
// #[macro_export]
// macro_rules! build_decls {
//     (@$decls:expr,) => {};

//     (@$decls:expr, $($ident:ident),* $(,)? : $typ:tt $($tail:tt)*) => {{
//         $(
//             let typ = $crate::build_typ!($typ);
//             if let Some(old_typ) = $decls.register(stringify!($ident), typ) {
//                 panic!(
//                     "trying to register identifier `{}` twice ({}/{})",
//                     stringify!($ident),
//                     old_typ,
//                     typ
//                 )
//             }
//         )*
//         build_decls!(@$decls, $($tail)*);
//     }};

//     ($($stuff:tt)*) => {{
//         let mut decls = $crate::Decls::new();
//         $crate::build_decls!(@decls, $($stuff)*);
//         decls
//     }};
// }

/// Builds a transition system.
#[macro_export]
macro_rules! build_trans {
    (
        decls {
            $($decls:tt)+
        }
        init: $init:tt
        trans: $trans:tt
        po_s: $($name:expr => $po:tt)+
    ) => {{
        let decls = $crate::build_decls!($($decls)*);
        let init = $crate::build_trans_expr!(stateless, decls, $init);
        let trans = $crate::build_trans_expr!(stateful, decls, $trans);
        let mut po_s = std::collections::BTreeMap::new();
        $(
            let name = $name;
            let expr = $crate::build_trans_expr!(stateless, decls, $po);
            if let Some(e) = po_s.insert(name.into(), expr) {
                panic!("found two proof obligations named `{}`", name)
            }
        )+
        $crate::Sys::new(decls, init, trans, po_s)
    }};
}
