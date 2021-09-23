//! Keywords of the language.

#![allow(non_upper_case_globals)]

crate::prelude!();

macro_rules! build_keywords {
    {
        $(
            $(#[$mod_meta:meta])*
            $mod_ident:ident {
                $(
                    $(#[$kw_meta:meta])*
                    $kw_ident:ident : $kw_str:expr
                ),*
                $(,)?
            }
        )*
    } => {
        $(
            $(#[$mod_meta])*
            pub mod $mod_ident {
                $(
                    $(#[$kw_meta])*
                    pub const $kw_ident: &str = $kw_str;
                )*
            }
        )*

        lazy_static::lazy_static! {
            /// Set of all the keywords.
            pub static ref all: Set<&'static str> = {
                let mut set = Set::new();
                $($(
                    let is_new = set.insert($kw_str);
                    if !is_new {
                        panic!("[internal] keyword `{}` is defined twice", $kw_str)
                    }
                )*)*
                set
            };
        }
    };
}

build_keywords! {
    /// Mikino-specific keywords.
    mkn {
        /// Variable declaration keyword.
        vars: "vars",
        /// Initial predicate declaration keyword.
        init: "init",
        /// Transition relation declaration keyword.
        trans: "trans",
        ite_if: "if",
        ite_then: "then",
        ite_else: "else",
    }
    /// SMT-LIB-specific keywords.
    smt_lib {
        /// `assert` keyword.
        assert: "assert",
        /// Constant declaration.
        dec_const: "declare-const",
    }
}
