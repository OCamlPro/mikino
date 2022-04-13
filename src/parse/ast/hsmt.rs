//! AST for the Human-SMT-LIB 2 (hsmt 2 for short) language.
//!
//! Hsmt 2 is subset of SMT-LIB 2 equipped with Rust-flavored syntax.

crate::prelude!();

use parse::ast::*;

/// Command trait.
pub trait CommandExt {
    /// True if the command is a query, *i.e.* produces a result.
    fn is_query(&self) -> bool;
    /// A short string description.
    fn desc(&self) -> String;
}

/// A sequence of commands between braces.
#[derive(Debug, Clone)]
pub struct Block<E, ME> {
    /// Block's content.
    pub content: Commands<E, ME>,
}
impl<E, ME> From<Commands<E, ME>> for Block<E, ME> {
    fn from(cs: Commands<E, ME>) -> Self {
        Self::new(cs)
    }
}
impl<E, ME> CommandExt for Block<E, ME> {
    fn is_query(&self) -> bool {
        self.content.is_query()
    }
    fn desc(&self) -> String {
        format!("block({})", self.content.len())
    }
}
impl<E, ME> ops::Index<usize> for Block<E, ME> {
    type Output = Command<E, ME>;
    fn index(&self, idx: usize) -> &Command<E, ME> {
        &self.content[idx]
    }
}
impl<E, ME> Block<E, ME> {
    /// Creates a new block.
    pub fn new(content: Commands<E, ME>) -> Self {
        Self { content }
    }
}

/// An assertion.
#[derive(Debug, Clone)]
pub struct Assert<E> {
    /// Expression to assert.
    pub expr: E,
}
impl<E> CommandExt for Assert<E> {
    fn is_query(&self) -> bool {
        false
    }
    fn desc(&self) -> String {
        format!("assert!")
    }
}

impl<E> Assert<E> {
    /// Constructor.
    pub fn new(expr: E) -> Self {
        Self { expr }
    }
}

/// Echoes something.
#[derive(Debug, Clone)]
pub struct Echo {
    /// Message.
    pub msg: String,
}
impl CommandExt for Echo {
    fn is_query(&self) -> bool {
        false
    }
    fn desc(&self) -> String {
        format!("echo(\"{}\")", self.msg)
    }
}

impl Echo {
    /// Constructor.
    pub fn new(msg: impl Into<String>) -> Self {
        Self { msg: msg.into() }
    }
}

/// Some constant declarations.
#[derive(Debug, Clone)]
pub struct Vars {
    /// Declaration span.
    pub span: Span,
    /// Some declarations.
    pub decls: trans::Decls,
}
impl CommandExt for Vars {
    fn is_query(&self) -> bool {
        false
    }
    fn desc(&self) -> String {
        format!("vars({})", self.decls.all().count())
    }
}

impl Vars {
    /// Constructor.
    pub fn new(span: impl Into<Span>, decls: trans::Decls) -> Self {
        Self {
            span: span.into(),
            decls,
        }
    }
}

/// A meta let-binding, used to memorize the result of a [`Query`].
#[derive(Debug, Clone)]
pub struct MLet {
    /// Identifier we're binding.
    pub lhs: Spn<String>,
    /// Command producing the value we're binding.
    pub rhs: CheckSat,
}
impl CommandExt for MLet {
    fn is_query(&self) -> bool {
        false
    }
    fn desc(&self) -> String {
        format!("meta-let({})", self.lhs.inner)
    }
}
impl MLet {
    /// Constructor.
    pub fn new(lhs: impl Into<Spn<String>>, rhs: CheckSat) -> Self {
        let lhs = lhs.into();
        Self { lhs, rhs }
    }
}

/// A check sat ([`Query`]).
#[derive(Debug, Clone)]
pub struct CheckSat {
    /// Keyword span.
    pub span: Span,
    /// Optional list of `declare-const`ed `Bool` identifiers to assume true in the check sat.
    pub assuming: Vec<Spn<String>>,
    /// Optional timeout.
    pub timeout: Option<time::Duration>,
}
impl CommandExt for CheckSat {
    fn is_query(&self) -> bool {
        true
    }
    fn desc(&self) -> String {
        format!("check-sat")
    }
}

impl CheckSat {
    /// Constructor.
    pub fn new(
        span: impl Into<Span>,
        assuming: Option<Vec<Spn<String>>>,
        timeout: Option<time::Duration>,
    ) -> Self {
        Self {
            span: span.into(),
            assuming: assuming.unwrap_or_else(Vec::new),
            timeout,
        }
    }
}

/// An if-then-else on a meta, boolean variable ([`Query`]).
///
/// `Ite` is a [`Query`] because it **can** produce a result. Namely, if all of its branches end
/// with a check sat.
#[derive(Debug, Clone)]
pub struct Ite<E, ME> {
    /// Span of the `if`.
    pub span: Span,
    /// Condition.
    ///
    /// The [`Expr`] variant is quite restrictive: it can only be a purely boolean term the leaves
    /// of which must all be meta-variables (of type bool). This is check by
    /// [`Self.check_cnd_expr`].
    pub cnd: Either<Spn<expr::MetaVar>, CheckSat>,
    /// Then branch.
    pub thn: Block<E, ME>,
    /// Else branch.
    pub els: Block<E, ME>,
    /// Otherwise branch, triggers on an `unknown` or `timeout` check sat result.
    pub otw: Option<Block<E, ME>>,
    /// Temporary fix for the `ME` type parameter not being used.
    _tmp: marker::PhantomData<ME>,
}
impl<E, ME> CommandExt for Ite<E, ME> {
    fn is_query(&self) -> bool {
        self.thn.is_query()
            && self.els.is_query()
            && self.otw.as_ref().map(Block::is_query).unwrap_or(true)
    }
    fn desc(&self) -> String {
        format!("ite")
    }
}
impl<E, ME> Ite<E, ME> {
    /// Unchecked constructor.
    pub fn new(
        span: impl Into<Span>,
        cnd: Either<Spn<expr::MetaVar>, CheckSat>,
        thn: Block<E, ME>,
        els: Block<E, ME>,
        otw: Option<Block<E, ME>>,
    ) -> Self {
        Self {
            span: span.into(),
            cnd,
            thn,
            els,
            otw,
            _tmp: marker::PhantomData,
        }
    }
}

// impl Ite<Expr, MExpr> {
//     /// Constructor, fails if `cnd` is an illegal condition (see [`Self.check_cnd_expr`]).
//     ///
//     /// Parameter `meta_env` is a function such that `meta_env(ident) = true` if `ident` is a
//     /// meta-variable in the current environment. See also [`Self.check_cnd_expr`].
//     pub fn new(
//         meta_env: impl FnMut(&str) -> bool,
//         cnd: Either<MExpr, CheckSat>,
//         thn: Commands<Expr, MExpr>,
//         els: Commands<Expr, MExpr>,
//         otw: Option<Commands<Expr, MExpr>>,
//     ) -> Result<Self, String> {
//         if let Either::Left(cnd) = &cnd {
//             Self::check_cnd_expr(cnd, meta_env)?
//         }
//         Ok(Self { cnd, thn, els, otw })
//     }

//     /// Checks that an [`Expr`] is a legal `Ite` condition.
//     ///
//     /// The expression is legal **iff**
//     /// - it is purely boolean, *i.e.* only uses boolean operators, and
//     /// - only mentions variables recognized by `meta_env`, or `True`/`False`.
//     pub fn check_cnd_expr(
//         cnd: &Expr,
//         mut meta_env: impl FnMut(&str) -> bool,
//     ) -> Result<(), String> {
//         let mut unknown_ids: Option<Set<&str>> = None;
//         let mut illegal_csts: Option<Set<&Cst>> = None;
//         cnd.fold(
//             |var: &Var| {
//                 if !meta_env(var.id()) {
//                     let _is_new = unknown_ids.get_or_insert_with(Set::new).insert(var.id());
//                 }
//             },
//             |cst: &Cst| match cst {
//                 Cst::B(_) => (),
//                 _ => {
//                     let _is_new = illegal_csts.get_or_insert_with(Set::new).insert(cst);
//                 }
//             },
//             // Can't actually check much here, since type-checking requires accessing the kids.
//             // **Currently**, applications cannot be non-bool without having non-bool leaves
//             // (cst/var), and we're checking for that. So it's most definitely likely to be fine.
//             |_op, _kid_accs| (),
//         );

//         let mut error = None;

//         // Populates `error` if needed, ending with a newline.
//         if let Some(unknown_ids) = unknown_ids {
//             let plural = if unknown_ids.is_empty() { "" } else { "s" };
//             let error = error.get_or_insert_with(|| String::with_capacity(203));
//             if illegal_csts.is_some() {
//                 error.push_str("- ")
//             }
//             error.push_str("unknown meta-variable");
//             error.push_str(plural);

//             let count = unknown_ids.len();
//             for (idx, id) in unknown_ids.into_iter().enumerate() {
//                 if idx == 0 {
//                     error.push_str(" `");
//                 } else {
//                     if idx + 1 == count {
//                         error.push_str(" and `");
//                     } else {
//                         error.push_str(", `");
//                     }
//                 }
//                 error.push_str(&id);
//                 error.push('`');
//             }
//             error.push('\n');
//         }

//         // Populates/augments `error if needed, ending with a newline.
//         if let Some(illegal_csts) = illegal_csts {
//             let plural = if illegal_csts.is_empty() { "" } else { "s" };
//             let needs_sep = error.is_some();
//             let error = error.get_or_insert_with(|| String::with_capacity(203));
//             error.push_str("\n");
//             if needs_sep {
//                 error.push_str("- ");
//             }
//             error.push_str("illegal non-boolean constant");
//             error.push_str(plural);

//             let count = illegal_csts.len();
//             for (idx, cst) in illegal_csts.into_iter().enumerate() {
//                 if idx == 0 {
//                     error.push_str(" `");
//                 } else {
//                     if idx + 1 == count {
//                         error.push_str(" and `");
//                     } else {
//                         error.push_str(", `");
//                     }
//                 }
//                 error.push_str(&cst.to_string());
//                 error.push('`');
//             }
//             error.push('\n');
//         }

//         if let Some(mut error) = error {
//             error.push_str(
//                 "\n\
// If-then-else conditions can only mention boolean operators and **meta**-variables,\n\
// i.e. variables obtained by `let <ident> = <query>`, where `<query>` is typically a\n\
// `check_sat`.\
//             	",
//             );
//             error.shrink_to_fit();
//             Err(error)
//         } else {
//             Ok(())
//         }
//     }
// }

/// Commands that can produce boolean results.
#[derive(Debug, Clone)]
pub enum Query<E, ME> {
    /// A block of commands.
    ///
    /// This query only produces a boolean result if its last command is a query.
    Block(Block<E, ME>),
    /// Good ol' check sat.
    CheckSat(CheckSat),
    /// If-then-else.
    ///
    /// This query only produces a boolean result if both its branches end with a [`CheckSat`].
    /// Note that trying to use result-less [`Ite`] as a result, in an [`MLet`] for instance, is a
    /// static error; not a runtime one.
    Ite(Ite<E, ME>),
}
impl<E, ME> CommandExt for Query<E, ME> {
    fn is_query(&self) -> bool {
        match self {
            Self::Block(b) => b.is_query(),
            Self::CheckSat(q) => q.is_query(),
            Self::Ite(q) => q.is_query(),
        }
    }
    fn desc(&self) -> String {
        match self {
            Self::Block(b) => b.desc(),
            Self::CheckSat(q) => q.desc(),
            Self::Ite(q) => q.desc(),
        }
    }
}

impl<E, ME> From<Block<E, ME>> for Query<E, ME> {
    fn from(b: Block<E, ME>) -> Self {
        Self::Block(b)
    }
}
impl<E, ME> From<CheckSat> for Query<E, ME> {
    fn from(c: CheckSat) -> Self {
        Self::CheckSat(c)
    }
}
impl<E, ME> From<Ite<E, ME>> for Query<E, ME> {
    fn from(ite: Ite<E, ME>) -> Self {
        Self::Ite(ite)
    }
}

/// A list of commands.
pub type Commands<E, ME> = Vec<Command<E, ME>>;
impl<E, ME> CommandExt for Commands<E, ME> {
    fn is_query(&self) -> bool {
        self.last().map(Command::is_query).unwrap_or(false)
    }
    fn desc(&self) -> String {
        format!("sequenc of commands")
    }
}

/// Enumerates RSmt 2 commands.
#[derive(Debug, Clone)]
pub enum Command<E, ME> {
    /// Constant declaration/definition.
    Vars(Vars),
    /// Meta-let, memorizes query results.
    MLet(MLet),
    /// Assert.
    Assert(Assert<E>),
    /// Echo.
    Echo(Echo),
    /// Commands that can produce boolean results.
    Query(Query<E, ME>),
}
impl<E, ME> CommandExt for Command<E, ME> {
    fn is_query(&self) -> bool {
        match self {
            Self::Vars(c) => c.is_query(),
            Self::MLet(c) => c.is_query(),
            Self::Assert(c) => c.is_query(),
            Self::Echo(c) => c.is_query(),
            Self::Query(q) => q.is_query(),
        }
    }
    fn desc(&self) -> String {
        match self {
            Self::Vars(c) => c.desc(),
            Self::MLet(c) => c.desc(),
            Self::Assert(c) => c.desc(),
            Self::Echo(c) => c.desc(),
            Self::Query(q) => q.desc(),
        }
    }
}

impl<E, ME> From<Vars> for Command<E, ME> {
    fn from(l: Vars) -> Self {
        Self::Vars(l)
    }
}
impl<E, ME> From<MLet> for Command<E, ME> {
    fn from(ml: MLet) -> Self {
        Self::MLet(ml)
    }
}
impl<E, ME> From<Assert<E>> for Command<E, ME> {
    fn from(a: Assert<E>) -> Self {
        Self::Assert(a)
    }
}
impl<E, ME> From<Echo> for Command<E, ME> {
    fn from(e: Echo) -> Self {
        Self::Echo(e)
    }
}

impl<E, ME> From<Query<E, ME>> for Command<E, ME> {
    fn from(q: Query<E, ME>) -> Self {
        Self::Query(q)
    }
}
impl<E, ME> From<Block<E, ME>> for Command<E, ME> {
    fn from(q: Block<E, ME>) -> Self {
        Self::Query(q.into())
    }
}
impl<E, ME> From<Ite<E, ME>> for Command<E, ME> {
    fn from(q: Ite<E, ME>) -> Self {
        Self::Query(q.into())
    }
}
impl<E, ME> From<CheckSat> for Command<E, ME> {
    fn from(q: CheckSat) -> Self {
        Self::Query(q.into())
    }
}
