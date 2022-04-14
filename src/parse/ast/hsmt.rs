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
    /// True if the command is guaranteed to end in a panic.
    fn panics(&self) -> bool;
}

/// A set-option.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetOption {
    /// Attribute key.
    pub key: Spn<String>,
    /// Attribute value.
    pub val: Spn<Either<Cst, String>>,
}
impl fmt::Display for SetOption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: ", self.key.inner)?;
        match &self.val.inner {
            Either::Left(cst) => cst.fmt(f),
            Either::Right(s) => s.fmt(f),
        }
    }
}
impl SetOption {
    /// Constructor.
    pub fn new(key: impl Into<Spn<String>>, val: Spn<Either<Cst, String>>) -> Self {
        Self {
            key: key.into(),
            val: val.into(),
        }
    }
}
/// A sequence of set-option-s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetOptions {
    /// Span of the `set_option!` keyword.
    pub span: Span,
    /// Sequence of set-options-s.
    pub content: Vec<SetOption>,
}
impl CommandExt for SetOptions {
    fn is_query(&self) -> bool {
        false
    }
    fn desc(&self) -> String {
        let mut s = format!("set_options!(");
        for (idx, opt) in self.content.iter().enumerate() {
            if idx > 0 {
                s.push_str(", ");
            }
            s.push_str(&opt.to_string());
        }
        s.push(')');
        s
    }
    fn panics(&self) -> bool {
        false
    }
}

impl SetOptions {
    /// Constructor.
    pub fn new(span: impl Into<Span>, content: Vec<SetOption>) -> Self {
        Self {
            span: span.into(),
            content,
        }
    }
}

/// A sequence of commands between braces.
#[derive(Debug, Clone, PartialEq, Eq)]
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
    fn panics(&self) -> bool {
        self.content.iter().any(Command::panics)
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assert<E> {
    /// Span.
    pub span: Span,
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
    fn panics(&self) -> bool {
        false
    }
}

impl<E> Assert<E> {
    /// Constructor.
    pub fn new(span: impl Into<Span>, expr: E) -> Self {
        Self {
            span: span.into(),
            expr,
        }
    }
}

/// Echoes something.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Echo {
    /// Message.
    pub msg: String,
}
impl CommandExt for Echo {
    fn is_query(&self) -> bool {
        false
    }
    fn desc(&self) -> String {
        format!("echo!(\"{}\")", self.msg)
    }
    fn panics(&self) -> bool {
        false
    }
}

impl Echo {
    /// Constructor.
    pub fn new(msg: impl Into<String>) -> Self {
        Self { msg: msg.into() }
    }
}

/// Panics with a message.
///
/// Note that a panic **is** a query. It can return anything since it does not return.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Panic {
    /// Span.
    pub span: Span,
    /// Message.
    pub msg: String,
}
impl CommandExt for Panic {
    fn is_query(&self) -> bool {
        true
    }
    fn desc(&self) -> String {
        format!("panic!(\"{}\")", self.msg)
    }
    fn panics(&self) -> bool {
        true
    }
}

impl Panic {
    /// Constructor.
    pub fn new(span: impl Into<Span>, msg: impl Into<String>) -> Self {
        Self {
            span: span.into(),
            msg: msg.into(),
        }
    }
}

/// Some constant declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
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
    fn panics(&self) -> bool {
        false
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
    fn panics(&self) -> bool {
        false
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
    fn panics(&self) -> bool {
        false
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
    fn panics(&self) -> bool {
        self.thn.panics()
            && self.els.panics()
            && self.otw.as_ref().map(|b| b.panics()).unwrap_or(true)
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

/// Commands that can produce boolean results.
#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// Panic.
    Panic(Panic),
}
impl<E, ME> CommandExt for Query<E, ME> {
    fn is_query(&self) -> bool {
        match self {
            Self::Block(b) => b.is_query(),
            Self::CheckSat(q) => q.is_query(),
            Self::Ite(q) => q.is_query(),
            Self::Panic(q) => q.is_query(),
        }
    }
    fn desc(&self) -> String {
        match self {
            Self::Block(b) => b.desc(),
            Self::CheckSat(q) => q.desc(),
            Self::Ite(q) => q.desc(),
            Self::Panic(q) => q.desc(),
        }
    }
    fn panics(&self) -> bool {
        match self {
            Self::Block(b) => b.panics(),
            Self::CheckSat(q) => q.panics(),
            Self::Ite(q) => q.panics(),
            Self::Panic(q) => q.panics(),
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
impl<E, ME> From<Panic> for Query<E, ME> {
    fn from(p: Panic) -> Self {
        Self::Panic(p)
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
    fn panics(&self) -> bool {
        self.iter().any(Command::panics)
    }
}

/// Enumerates RSmt 2 commands.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command<E, ME> {
    /// Set-option-s.
    SetOptions(SetOptions),
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
            Self::SetOptions(c) => c.is_query(),
            Self::Vars(c) => c.is_query(),
            Self::MLet(c) => c.is_query(),
            Self::Assert(c) => c.is_query(),
            Self::Echo(c) => c.is_query(),
            Self::Query(q) => q.is_query(),
        }
    }
    fn desc(&self) -> String {
        match self {
            Self::SetOptions(c) => c.desc(),
            Self::Vars(c) => c.desc(),
            Self::MLet(c) => c.desc(),
            Self::Assert(c) => c.desc(),
            Self::Echo(c) => c.desc(),
            Self::Query(q) => q.desc(),
        }
    }
    fn panics(&self) -> bool {
        match self {
            Self::SetOptions(c) => c.panics(),
            Self::Vars(c) => c.panics(),
            Self::MLet(c) => c.panics(),
            Self::Assert(c) => c.panics(),
            Self::Echo(c) => c.panics(),
            Self::Query(q) => q.panics(),
        }
    }
}

impl<E, ME> From<SetOptions> for Command<E, ME> {
    fn from(l: SetOptions) -> Self {
        Self::SetOptions(l)
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
impl<E, ME> From<Panic> for Command<E, ME> {
    fn from(q: Panic) -> Self {
        Self::Query(q.into())
    }
}
impl<E, ME> From<CheckSat> for Command<E, ME> {
    fn from(q: CheckSat) -> Self {
        Self::Query(q.into())
    }
}
