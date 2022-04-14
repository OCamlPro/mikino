//! HSmt 2 scripts.

prelude!();

use expr::{Expr, MExpr};
use parse::ast::hsmt::*;

use crate::parse::PError;

pub mod build;
pub mod frame;

// use frame::Frame;

/// Result of running a script.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// Everything went fine.
    Success,
    /// Panic.
    Panic(parse::Span, String),
}

/// A step result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Step {
    /// Check sat result.
    CheckRes(parse::Span, bool),
    /// Something to print.
    Echo(Echo),
    /// Nothing observable happened.
    Nothing,
    /// Done, with an outcome.
    Done(Outcome),
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

    /// Turns itself into either a step result or an outcome.
    ///
    /// Used for check sat results not caught by a meta-variable.
    pub fn handle(self) -> Either<Step, Outcome> {
        match self.res {
            CheckSatResEnum::True => Either::Left(Step::CheckRes(self.span, true)),
            CheckSatResEnum::False => Either::Left(Step::CheckRes(self.span, false)),
            CheckSatResEnum::Timeout => {
                Either::Right(Outcome::Panic(self.span, "uncaught timeout".into()))
            }
            CheckSatResEnum::Unknown => {
                Either::Right(Outcome::Panic(self.span, "uncaught unknown result".into()))
            }
        }
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
pub enum CurrentCmd<'s> {
    /// Command.
    C(&'s Command<Expr, MExpr>),
    /// Query.
    Q(&'s Query<Expr, MExpr>),
    /// Check sat.
    Cs(&'s CheckSat),
}
impl<'s> From<&'s Command<Expr, MExpr>> for CurrentCmd<'s> {
    fn from(c: &'s Command<Expr, MExpr>) -> Self {
        Self::C(c)
    }
}
impl<'s> From<&'s Query<Expr, MExpr>> for CurrentCmd<'s> {
    fn from(c: &'s Query<Expr, MExpr>) -> Self {
        Self::Q(c)
    }
}
impl<'s> From<&'s CheckSat> for CurrentCmd<'s> {
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
    /// Stores the final outcome.
    outcome: Option<Outcome>,
    /// Result of the current step.
    step_res: Step,
    /// Current command.
    curr: CurrentCmd<'s>,
}
impl<'s> Script<'s> {
    /// Constructor.
    pub fn new(
        z3_cmd: impl AsRef<str>,
        tee: Option<impl AsRef<str>>,
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
            outcome: None,
            step_res: Step::Nothing,
            curr,
        })
    }

    /// Set-options.
    pub fn set_options(&mut self, opts: &SetOptions) -> Res<()> {
        self.inner_set_options(opts).map_err(|e| {
            e.chain_err(|| PError::new_error(opts.span, self.txt, "while handling these options"))
        })
    }
    fn inner_set_options(&mut self, opts: &SetOptions) -> Res<()> {
        for opt in opts.content.iter() {
            match opt.val.inner.as_ref() {
                Either::Left(cst) => self.solver.set_option(&opt.key, cst)?,
                Either::Right(s) => self.solver.set_option(&opt.key, format!("\"{}\"", s))?,
            }
        }
        Ok(())
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
        Ok(())
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
        self.stack.push(frame.into());
        Ok(())
    }

    /// Block.
    pub fn block(&mut self, block: &'s Block<Expr, MExpr>) -> Res<()> {
        self.stack.push(frame::Block::new(block).into());
        Ok(())
    }

    /// Panic.
    pub fn panic(&mut self, panic: &'s Panic) -> Res<()> {
        debug_assert_eq!(self.outcome, None);
        self.outcome = Some(Outcome::Panic(panic.span, panic.msg.clone()));
        Ok(())
    }

    /// Echo.
    pub fn echo(&mut self, echo: &'s Echo) -> Res<()> {
        debug_assert_eq!(self.step_res, Step::Nothing);
        self.step_res = Step::Echo(echo.clone());
        Ok(())
    }

    /// Assertion.
    pub fn assert(&mut self, a: &'s Assert<Expr>) -> Res<()> {
        match self.solver.assert_with(&a.expr, 0) {
            Ok(()) => (),
            Err(e) => {
                return Err(PError::new("while handling this assert!", a.span)
                    .into_error(self.txt)
                    .chain_err(|| e));
            }
        }
        Ok(())
    }

    /// Performs an interpretation step.
    pub fn step(&mut self) -> Res<Step> {
        debug_assert_eq!(self.step_res, Step::Nothing);
        if let Some(res) = self.outcome.as_ref() {
            return Ok(Step::Done(res.clone()));
        }

        // do stuff

        if let Some(res) = self.outcome.as_ref() {
            Ok(Step::Done(res.clone()))
        } else {
            Ok(mem::replace(&mut self.step_res, Step::Nothing))
        }
    }

    /// Goes up the stack, given a result.
    pub fn go_up(&mut self, qres: QueryRes) -> Res<()> {
        use frame::{Command as C, Query as Q};
        match self.stack.pop() {
            None => {
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
            }
            Some(C::Query(Q::Block(mut b))) => {
                if let Some(cmd) = b.next() {
                    self.curr = cmd.into();
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
