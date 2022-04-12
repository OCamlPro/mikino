//! AST for the Human-SMT-LIB 2 (hsmt 2 for short) language.
//!
//! Hsmt 2 is subset of SMT-LIB 2 equipped with Rust-flavored syntax.

crate::prelude!();

use expr::*;
use parse::ast::*;

/// A constant declaration/definition.
///
/// - If `self.rhs.is_none()`, then this is just a `declare-const`;
/// - if `self.rhs = Some(expr)`, this is a `declare-const` followed by an assertion that `lhs =
///   rhs`.
#[derive(Debug, Clone)]
pub struct Let {
    /// Identifier for the constant.
    pub lhs: String,
    /// Type of the constant.
    pub typ: Typ,
    /// Optional value, produces an assertion that `lhs = rhs`.
    pub rhs: Option<Expr>,
}

/// A meta let-binding, used to memorize the result of a [`Query`].
#[derive(Debug, Clone)]
pub struct MLet {
    /// Identifier we're binding.
    pub lhs: String,
    /// Command producing the value we're binding.
    pub rhs: Query,
}

/// A check sat ([`Query`]).
#[derive(Debug, Clone)]
pub struct CheckSat {
    /// Optional list of `declare-const`ed `Bool` identifiers to assume true in the check sat.
    pub assuming: Vec<String>,
}

/// An if-then-else on a meta, boolean variable ([`Query`]).
///
/// `Ite` is a [`Query`] because
#[derive(Debug, Clone)]
pub struct Ite {
    /// Condition.
    ///
    /// The [`Expr`] variant is quite restrictive: it can only be a purely boolean term the leaves
    /// of which must all be meta-variables (of type bool). This is check by
    /// [`Self.check_cnd_expr`].
    ///
    /// The [`Query`] variant is boxed because `Ite` is itself a `Query`. We need this `Box` to
    /// prevent them from being DSTs (Dynamically Sized Type-s).
    pub cnd: Either<Expr, Box<Query>>,
    /// Then branch.
    pub thn: Expr,
    /// Else branch.
    pub els: Expr,
}
impl Ite {
    /// Constructor, fails if `cnd` is an illegal condition (see [`Self.check_cnd_expr`]).
    ///
    /// Parameter `meta_env` is a function such that `meta_env(ident) = true` if `ident` is a
    /// meta-variable in the current environment. See also [`Self.check_cnd_expr`].
    pub fn new(
        meta_env: impl FnMut(&str) -> bool,
        cnd: Either<Expr, Query>,
        thn: Expr,
        els: Expr,
    ) -> Result<Self, String> {
        let cnd = cnd.map_right(Box::new);
        if let Either::Left(cnd) = &cnd {
            Self::check_cnd_expr(cnd, meta_env)?
        }
        Ok(Self { cnd, thn, els })
    }

    /// Checks that an [`Expr`] is a legal `Ite` condition.
    ///
    /// The expression is legal **iff**
    /// - it is purely boolean, *i.e.* only uses boolean operators, and
    /// - only mentions variables recognized by `meta_env`, or `True`/`False`.
    pub fn check_cnd_expr(
        cnd: &Expr,
        mut meta_env: impl FnMut(&str) -> bool,
    ) -> Result<(), String> {
        let mut unknown_ids: Option<Set<&str>> = None;
        let mut illegal_csts: Option<Set<&Cst>> = None;
        cnd.fold(
            |var: &Var| {
                if !meta_env(var.id()) {
                    let _is_new = unknown_ids.get_or_insert_with(Set::new).insert(var.id());
                }
            },
            |cst: &Cst| match cst {
                Cst::B(_) => (),
                _ => {
                    let _is_new = illegal_csts.get_or_insert_with(Set::new).insert(cst);
                }
            },
            // Can't actually check much here, since type-checking requires accessing the kids.
            // **Currently**, applications cannot be non-bool without having non-bool leaves
            // (cst/var), and we're checking for that. So it's most definitely likely to be fine.
            |_op, _kid_accs| (),
        );

        let mut error = None;

        // Populates `error` if needed, ending with a newline.
        if let Some(unknown_ids) = unknown_ids {
            let plural = if unknown_ids.is_empty() { "" } else { "s" };
            let error = error.get_or_insert_with(|| String::with_capacity(203));
            if illegal_csts.is_some() {
                error.push_str("- ")
            }
            error.push_str("unknown meta-variable");
            error.push_str(plural);

            let count = unknown_ids.len();
            for (idx, id) in unknown_ids.into_iter().enumerate() {
                if idx == 0 {
                    error.push_str(" `");
                } else {
                    if idx + 1 == count {
                        error.push_str(" and `");
                    } else {
                        error.push_str(", `");
                    }
                }
                error.push_str(&id);
                error.push('`');
            }
            error.push('\n');
        }

        // Populates/augments `error if needed, ending with a newline.
        if let Some(illegal_csts) = illegal_csts {
            let plural = if illegal_csts.is_empty() { "" } else { "s" };
            let needs_sep = error.is_some();
            let error = error.get_or_insert_with(|| String::with_capacity(203));
            error.push_str("\n");
            if needs_sep {
                error.push_str("- ");
            }
            error.push_str("illegal non-boolean constant");
            error.push_str(plural);

            let count = illegal_csts.len();
            for (idx, cst) in illegal_csts.into_iter().enumerate() {
                if idx == 0 {
                    error.push_str(" `");
                } else {
                    if idx + 1 == count {
                        error.push_str(" and `");
                    } else {
                        error.push_str(", `");
                    }
                }
                error.push_str(&cst.to_string());
                error.push('`');
            }
            error.push('\n');
        }

        if let Some(mut error) = error {
            error.push_str(
                "\n\
If-then-else conditions can only mention boolean operators and **meta**-variables,\n\
i.e. variables obtained by `let <ident> = <query>`, where `<query>` is typically a\n\
`check_sat`.\
            	",
            );
            error.shrink_to_fit();
            Err(error)
        } else {
            Ok(())
        }
    }
}

/// Enumerates RSmt 2 commands.
#[derive(Debug, Clone)]
pub enum Command {
    /// Constant declaration/definition.
    Let(Let),
    /// Meta-let, memorizes query results.
    MLet(MLet),
    /// Commands that can produce boolean results.
    Query(Query),
}

/// Commands that can produce boolean results.
#[derive(Debug, Clone)]
pub enum Query {
    /// Good ol' check sat.
    CheckSat(CheckSat),
    /// If-then-else.
    ///
    /// This query only produces a boolean result if both its branches end with a [`CheckSat`].
    /// Note that trying to use result-less [`Ite`] as a result, in an [`MLet`] for instance, is a
    /// static error; not a runtime one.
    Ite(Ite),
}
