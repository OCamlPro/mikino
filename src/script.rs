//! HSmt 2 scripts.

prelude!();

use crate::parse::PError;

use expr::{Expr, MExpr};
use frame::Frame;
use parse::ast::hsmt::*;

pub mod build;
pub mod frame;

const DEBUG: bool = false;

// use frame::Frame;

/// Result of running a script.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// Everything went fine.
    Success,
    /// Panic.
    Panic(parse::Span, String),
}
impl Outcome {
    /// Turns itself in a pretty string representation.
    pub fn pretty(&self, txt: &str, style: impl Style) -> String {
        match self {
            Self::Success => style.green("success").to_string(),
            Self::Panic(span, msg) => {
                format!(
                    "execution {} with `{}` {}",
                    style.red("panicked"),
                    msg,
                    span.pretty_ml_of(txt, style, ""),
                )
            }
        }
    }
}

/// A step result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Step {
    /// Check sat result.
    CheckRes(parse::Span, CheckSatResEnum),
    /// Something to print.
    Echo(Echo),
    /// Nothing observable happened.
    Nothing,
    /// Done, with an outcome.
    Done(Outcome),
}
impl Step {
    /// Updates a step result.
    pub fn update(&mut self, step: impl Into<Step>) -> Res<()> {
        let step = step.into();
        *self = match (&self, step) {
            (Self::Nothing, step) => step,
            (_, Self::Nothing) => return Ok(()),
            (lft, rgt) => {
                bail!("[fatal] illegal `Step::update({:?}, {:?})`", lft, rgt)
            }
        };
        Ok(())
    }

    /// Pretty representation.
    pub fn pretty(&self, txt: &str, style: impl Style) -> Option<String> {
        let s = match self {
            Self::CheckRes(span, check_res) => {
                let (_, line, col, _, _) = span.pretty_of(txt);
                let res = match check_res {
                    CheckSatResEnum::True => style.green("sat"),
                    CheckSatResEnum::False => style.green("unsat"),
                    CheckSatResEnum::Timeout => style.red("timeout"),
                    CheckSatResEnum::Unknown => style.red("unknown"),
                };
                format!(
                    "[{}@{}] {}",
                    style.under("check_sat"),
                    style.bold(&format!("{}:{}", line, col)),
                    res,
                )
            }
            Self::Echo(msg) => {
                let (_, line, col, _, _) = msg.span.pretty_of(txt);
                format!(
                    "[{}@{}] {}",
                    style.under("echo"),
                    style.bold(&format!("{}:{}", line, col)),
                    msg.msg,
                )
            }
            Self::Nothing => {
                return None;
            }
            Self::Done(out) => out.pretty(txt, style),
        };
        Some(s)
    }

    /// True if the step result is nothing.
    pub fn is_nothing(&self) -> bool {
        match self {
            Self::Nothing => true,
            Self::Echo(_) | Self::CheckRes(_, _) | Self::Done(_) => false,
        }
    }
}
impl From<Outcome> for Step {
    fn from(out: Outcome) -> Self {
        Self::Done(out)
    }
}
impl From<CheckSatRes> for Step {
    fn from(c: CheckSatRes) -> Self {
        Self::CheckRes(c.span, c.res)
    }
}
impl From<QueryRes> for Step {
    fn from(res: QueryRes) -> Self {
        match res {
            QueryRes::None => Self::Nothing,
            QueryRes::CheckSat(c) => c.into(),
        }
    }
}

/// A check sat result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckSatResEnum {
    /// True result.
    True,
    /// False result.
    False,
    /// Timeout, no result.
    Timeout,
    /// Unknown result.
    Unknown,
}
impl fmt::Display for CheckSatResEnum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::True => "sat",
            Self::False => "unsat",
            Self::Timeout => "timeout",
            Self::Unknown => "unknown",
        };
        s.fmt(f)
    }
}

/// A check sat result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckSatRes {
    /// Span of the check sat.
    pub span: parse::Span,
    /// Result.
    pub res: CheckSatResEnum,
}
impl CheckSatRes {
    /// Turns itself into a boolean, if possible.
    pub fn to_bool(&self) -> Option<bool> {
        match self.res {
            CheckSatResEnum::True => Some(true),
            CheckSatResEnum::False => Some(false),
            CheckSatResEnum::Timeout | CheckSatResEnum::Unknown => None,
        }
    }

    /// Creates itself from a check-sat result.
    pub fn new(span: impl Into<parse::Span>, check_res: SmtRes<bool>) -> Res<Self> {
        let span = span.into();
        let res = match check_res {
            Ok(true) => CheckSatResEnum::True,
            Ok(false) => CheckSatResEnum::False,
            Err(e) => {
                use rsmt2::errors::ErrorKind as EK;
                match e.kind() {
                    EK::Unknown => CheckSatResEnum::Unknown,
                    EK::Timeout => CheckSatResEnum::Timeout,
                    _ => return Err(e.into()),
                }
            }
        };
        Ok(Self { span, res })
    }
}

/// A query result.
#[derive(Debug, Clone)]
pub enum QueryRes {
    /// Check sat result.
    CheckSat(CheckSatRes),
    /// No result.
    None,
}
impl From<CheckSatRes> for QueryRes {
    fn from(res: CheckSatRes) -> Self {
        Self::CheckSat(res)
    }
}
impl QueryRes {
    /// Creates itself from a check-sat result.
    pub fn from_check_sat(span: impl Into<parse::Span>, check_res: SmtRes<bool>) -> Res<Self> {
        let span = span.into();
        let res = match check_res {
            Ok(true) => CheckSatResEnum::True,
            Ok(false) => CheckSatResEnum::False,
            Err(e) => {
                use rsmt2::errors::ErrorKind as EK;
                match e.kind() {
                    EK::Unknown => CheckSatResEnum::Unknown,
                    EK::Timeout => CheckSatResEnum::Timeout,
                    _ => return Err(e.into()),
                }
            }
        };
        Ok(Self::CheckSat(CheckSatRes { span, res }))
    }
}

/// Current command.
#[derive(Debug, Clone)]
pub enum CurrentCmd<'s, E, ME> {
    /// Command.
    C(&'s Command<E, ME>),
    /// Block.
    B(&'s Block<E, ME>),
    /// Query.
    Q(&'s Query<E, ME>),
    /// Check sat.
    Cs(&'s CheckSat),
}
/// Alias for a script's current command.
pub type CurrCmd<'s> = CurrentCmd<'s, Expr, MExpr>;
impl<'s, E, ME> From<&'s Command<E, ME>> for CurrentCmd<'s, E, ME> {
    fn from(c: &'s Command<E, ME>) -> Self {
        Self::C(c)
    }
}
impl<'s, E, ME> From<&'s Block<E, ME>> for CurrentCmd<'s, E, ME> {
    fn from(b: &'s Block<E, ME>) -> Self {
        Self::B(b)
    }
}
impl<'s, E, ME> From<&'s Query<E, ME>> for CurrentCmd<'s, E, ME> {
    fn from(c: &'s Query<E, ME>) -> Self {
        Self::Q(c)
    }
}
impl<'s, E, ME> From<&'s CheckSat> for CurrentCmd<'s, E, ME> {
    fn from(c: &'s CheckSat) -> Self {
        Self::Cs(c)
    }
}

/// A script is a sequence of [`Command`]s and a *meta-environment*.
///
/// The *meta-environment* stores *meta-variables* and the values they have. A *meta-variable*
/// is a script-level (not SMT-level) variable that stores the result of a [`Query`]. Currently,
/// this amounts to the boolean result of a check sat.
///
/// We do not store SMT-level variables here as we already checked all expressions are legal,
/// regardless of branching. So expressions should always be legal at SMT-level too.
pub struct Script<'s> {
    /// Input text.
    txt: &'s str,
    /// Solver.
    pub solver: Solver,
    /// Original commands, the full script.
    pub script: &'s Command<Expr, MExpr>,
    /// Stack of command frames (derivatives).
    stack: Vec<frame::Command<'s, Expr, MExpr>>,
    /// Meta-environment.
    meta_env: Map<String, CheckSatRes>,
    /// Current result, indicates we're going up.
    res: Option<QueryRes>,
    /// Result of the current step.
    step_res: Step,
    /// Outcome, this is not `None` iff we're done.
    outcome: Option<Outcome>,
    /// Current command.
    curr: CurrCmd<'s>,
}
impl<'s> Script<'s> {
    /// Constructor.
    pub fn new(
        z3_cmd: impl AsRef<str>,
        tee: Option<&str>,
        script: &'s Command<Expr, MExpr>,
        txt: &'s str,
    ) -> Res<Self> {
        let solver = Solver::new(z3_cmd, tee)?;
        let stack = Vec::with_capacity(17);
        let curr = script.into();
        Ok(Self {
            txt,
            solver,
            script,
            stack,
            meta_env: Map::new(),
            res: None,
            step_res: Step::Nothing,
            curr,
            outcome: None,
        })
    }

    /// Sets the internal `res` to `Some(QueryRes::None)`, indicating we must go up.
    pub fn go_up_none(&mut self) -> Res<()> {
        self.go_up_with(QueryRes::None)
    }
    /// Sets the internal `res` to `Some(QueryRes::None)`, indicating we must go up.
    pub fn go_up_with(&mut self, res: QueryRes) -> Res<()> {
        let _prev = mem::replace(&mut self.res, Some(res));
        if let Some(res) = _prev {
            bail!("[fatal] overwriting *go_up* result {:?}", res)
        }
        Ok(())
    }

    /// Sets the internal step result.
    pub fn set_step_res(&mut self, step: impl Into<Step>) -> Res<()> {
        let _prev = mem::replace(&mut self.step_res, step.into());
        if !_prev.is_nothing() {
            bail!("[fatal] overwriting *step_res* result {:?}", _prev)
        }
        Ok(())
    }

    /// Set-options.
    pub fn set_options(&mut self, opts: &SetOptions) -> Res<()> {
        self.inner_set_options(opts).map_err(|e| {
            e.chain_err(|| PError::new_error(opts.span, self.txt, "while handling these options"))
        })
    }
    fn inner_set_options(&mut self, opts: &SetOptions) -> Res<()> {
        for opt in opts.content.iter() {
            let key = format!(":{}", opt.key.inner);
            match opt.val.inner.as_ref() {
                Either::Left(cst) => self.solver.set_option(&key, cst)?,
                Either::Right(s) => self.solver.set_option(&key, format!("\"{}\"", s))?,
            }
        }
        self.go_up_none()
    }

    /// Constant declarations.
    pub fn decl_vars(&mut self, vars: &Vars) -> Res<()> {
        self.inner_decl_vars(vars).map_err(|e| {
            e.chain_err(|| {
                PError::new_error(vars.span, self.txt, "while handling these declarations")
            })
        })
    }
    fn inner_decl_vars(&mut self, vars: &Vars) -> Res<()> {
        for var in vars.decls.all() {
            self.solver.declare_const(var.id(), var.typ())?;
        }
        self.go_up_none()
    }

    /// Check-sat.
    pub fn check_sat(&mut self, check: &CheckSat) -> Res<QueryRes> {
        self.inner_check_sat(check).map_err(|e| {
            e.chain_err(|| PError::new_error(check.span, self.txt, "while handling this check-sat"))
        })
    }
    fn inner_check_sat(&mut self, check: &CheckSat) -> Res<QueryRes> {
        let res = if check.assuming.is_empty() {
            self.solver.check_sat()
        } else {
            self.solver
                .check_sat_assuming(check.assuming.iter().map(|s| &s.inner))
        };
        QueryRes::from_check_sat(check.span, res)
    }

    /// If-then-else.
    pub fn ite(&mut self, ite: &'s Ite<Expr, MExpr>, check_res: Option<CheckSatRes>) -> Res<()> {
        self.inner_ite(ite, check_res).map_err(|e| {
            e.chain_err(|| {
                PError::new_error(ite.span, self.txt, "while handling this if-then-else")
            })
        })
    }
    fn inner_ite(&mut self, ite: &'s Ite<Expr, MExpr>, check_res: Option<CheckSatRes>) -> Res<()> {
        macro_rules! doit {
            ($res:expr) => {
                match $res {
                    CheckSatResEnum::True => frame::Ite::new_thn(ite)?,
                    CheckSatResEnum::False => frame::Ite::new_els(ite)?,
                    CheckSatResEnum::Timeout | CheckSatResEnum::Unknown => {
                        frame::Ite::new_otw(ite)?
                    }
                }
            };
        }
        let frame = match &ite.cnd {
            Either::Left(meta) => {
                let val = self.meta_env.get(&meta.inner.ident).ok_or_else(|| {
                    PError::new_error(meta.span, self.txt, "[fatal] unknown meta-variable")
                })?;
                doit!(val.res)
            }
            Either::Right(_) => match check_res {
                None => frame::Ite::new_cnd(ite)?,
                Some(res) => doit!(res.res),
            },
        };
        self.curr = frame.current()?;
        self.stack.push(frame.into());
        Ok(())
    }

    /// Block.
    pub fn block(&mut self, block: &'s Block<Expr, MExpr>) -> Res<()> {
        let mut frame = frame::Block::new(block);
        if let Some(next) = frame.next() {
            self.curr = next.into();
            self.stack.push(frame.into());
        } else {
            self.res = Some(QueryRes::None);
        }
        Ok(())
    }

    /// Panic.
    pub fn panic(&mut self, panic: &'s Panic) -> Res<()> {
        self.set_step_res(Outcome::Panic(panic.span, panic.msg.clone()))
    }

    /// Echo.
    pub fn echo(&mut self, echo: &'s Echo) -> Res<()> {
        self.set_step_res(Step::Echo(echo.clone()))?;
        self.go_up_none()
    }

    /// Assertion.
    pub fn assert(&mut self, a: &'s Assert<Expr>) -> Res<()> {
        match self.solver.assert_with(&a.expr, ()) {
            Ok(()) => (),
            Err(e) => {
                return Err(PError::new("while handling this assert!", a.span)
                    .into_error(self.txt)
                    .chain_err(|| e));
            }
        }
        self.go_up_none()
    }

    /// Meta-variable.
    pub fn mlet(&mut self, ml: &'s MLet) -> Res<()> {
        let frame = frame::Command::MLet(frame::MLet::new(ml));
        self.curr = frame.current()?;
        self.stack.push(frame);
        Ok(())
    }

    /// Performs an interpretation step.
    pub fn step(&mut self) -> Res<Step> {
        if DEBUG {
            println!();
        }
        debug_assert!(self.step_res.is_nothing());
        if let Some(res) = self.outcome.as_ref() {
            if DEBUG {
                println!("> got a res");
            }
            return Ok(Step::Done(res.clone()));
        }

        // Are we going up?
        if let Some(qres) = mem::replace(&mut self.res, None) {
            if DEBUG {
                println!("> going up {:?}", qres);
                if let Some(frame) = self.stack.last() {
                    for line in format!("{:#?}", frame).lines() {
                        println!("  {}", line);
                    }
                }
            }
            self.go_up(qres)?
        } else {
            if DEBUG {
                println!("> going down {:?}", self.curr);
            }
            self.go_down()?
        }

        let step = mem::replace(&mut self.step_res, Step::Nothing);
        match &step {
            Step::Done(res) => {
                self.outcome = Some(res.clone());
            }
            _ => (),
        }
        Ok(step)
    }

    /// Goes down the current command.
    pub fn go_down(&mut self) -> Res<()> {
        match self.curr {
            CurrentCmd::C(cmd) => self.go_down_cmd(cmd),
            CurrentCmd::B(b) => self.block(b),
            CurrentCmd::Q(q) => self.go_down_query(q),
            CurrentCmd::Cs(check) => self.go_down_check_sat(check),
        }
    }
    /// Goes down a command.
    pub fn go_down_cmd(&mut self, cmd: &'s Command<Expr, MExpr>) -> Res<()> {
        match cmd {
            Command::SetOptions(opts) => self.set_options(opts),
            Command::Echo(e) => self.echo(e),
            Command::Vars(vars) => self.decl_vars(vars),
            Command::MLet(mlet) => self.mlet(mlet),
            Command::Assert(a) => self.assert(a),
            Command::Query(q) => self.go_down_query(q),
        }
    }
    /// Goes down a query.
    pub fn go_down_query(&mut self, query: &'s Query<Expr, MExpr>) -> Res<()> {
        match query {
            Query::Block(block) => self.block(block),
            Query::CheckSat(c) => self.go_down_check_sat(c),
            Query::Ite(ite) => self.ite(ite, None),
            Query::Panic(panic) => self.panic(panic),
        }
    }
    /// Goes down a check sat.
    pub fn go_down_check_sat(&mut self, check_sat: &'s CheckSat) -> Res<()> {
        let res = self.check_sat(check_sat)?;
        self.go_up_with(res)
    }

    /// Goes up the stack, given a result.
    pub fn go_up(&mut self, qres: QueryRes) -> Res<()> {
        debug_assert!(self.step_res.is_nothing());
        use frame::{Command as C, Query as Q};
        match self.stack.pop() {
            None => {
                self.step_res.update(qres)?;
                self.outcome = Some(Outcome::Success);
            }
            Some(C::MLet(mlet)) => {
                let s = &mlet.mlet.lhs;
                match qres {
                    QueryRes::CheckSat(res) => {
                        let _prev = self.meta_env.insert(s.inner.clone(), res);
                    }
                    QueryRes::None => {
                        bail!(PError::new_error(
                            s.span,
                            self.txt,
                            "[fatal] no result to set this meta-variabl to",
                        ))
                    }
                }
                self.go_up_none()?
            }
            Some(C::Query(Q::Block(mut b))) => {
                if let Some(cmd) = b.next() {
                    self.curr = cmd.into();
                    self.stack.push(b.into());
                    self.step_res.update(qres)?;
                } else {
                    self.res = Some(qres);
                }
            }
            Some(C::Query(Q::Ite(ite))) => {
                let (ite, pos) = (ite.ite, ite.pos);
                use frame::ItePos as P;
                match pos {
                    P::Cnd => match qres {
                        QueryRes::None => bail!(PError::new_error(
                            ite.span,
                            self.txt,
                            "[fatal] condition of if-then-else produced no result"
                        )),
                        QueryRes::CheckSat(check) => self.ite(ite, Some(check))?,
                    },
                    P::Thn | P::Els | P::Otw => {
                        self.res = Some(qres);
                    }
                }
            }
        }
        Ok(())
    }
}
