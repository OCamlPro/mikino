//! Types and helpers to check a transition system.

crate::prelude!();

use rsmt2::{print::Expr2Smt, SmtConf};

use expr::{Expr, Var};
use trans::Sys;

pub mod cexs;

pub use cexs::{Cexs, SmtParser, Solver};

/// Aggregrates properties that are considered "ok" and properties that have been falsified.
///
/// This type is used by induction (both in base and step), and BMC. Hence, the meaning of "ok"
/// depends on the context. For instance, a property is "ok"
///
/// - in base if it holds in the initial states,
/// - in step if it is inductive,
/// - in BMC if no falsification has been found for it **yet**.
///
/// In one of these three contexts, a property "has been falsified" if it is not "ok".
///
/// **NB**: A [new] `CheckRes` has all properties of the system considered "ok".
///
/// [new]: #method.new
#[derive(Debug, Clone)]
pub struct CheckRes<'s> {
    /// Properties that are considered "ok".
    pub okay: Set<&'s String>,
    /// Properties for which a counterexample has been found.
    pub cexs: Cexs<'s>,
}
impl<'s> CheckRes<'s> {
    /// Constructor.
    ///
    /// Produces a `CheckRes` where all the POs are "ok".
    pub fn new(sys: &'s Sys) -> Self {
        let okay: Set<&'s String> = sys.po_s().keys().collect();
        Self {
            okay: okay.into(),
            cexs: Cexs::new(),
        }
    }

    /// True if all POs have been falsified.
    pub fn all_falsified(&self) -> bool {
        self.okay.is_empty()
    }
    /// True if some POs have been falsified.
    pub fn has_falsifications(&self) -> bool {
        !self.cexs.is_empty()
    }

    /// Registers a falsification.
    ///
    /// # Errors
    ///
    /// - when `po` does not belong to `self.okay`;
    /// - when a falsification for `po` has already been registered.
    pub fn register_falsification(&mut self, po: &'s String, solver: &mut Solver) -> Res<()> {
        if self.cexs.contains_key(po) {
            bail!("trying to register PO `{}` as falsified twice")
        }
        if !self.okay.iter().any(|ok_po| *ok_po == po) {
            bail!("trying to register unknown PO `{}` as falsified")
        }

        self.cexs.insert_falsification(po, solver)?;
        let was_there = self.okay.remove(po);
        if !was_there {
            bail!("trying to to register unknown PO `{}` as falsified", po)
        }

        Ok(())
    }
}

macro_rules! wrap {
    (
        $(
            $(#[$meta:meta])*
            $ty_name:ident
        ),* $(,)?
    ) => ($(
        $(#[$meta])*
        pub struct $ty_name<'sys> {
            /// Internal result.
            res: CheckRes<'sys>,
        }
        impl<'sys> $ty_name<'sys> {
            /// Inner result accessor (borrow).
            pub fn as_inner(&self) -> &CheckRes<'sys> {
                &self.res
            }
            /// Inner result accessor (move).
            pub fn into_inner(self) -> CheckRes<'sys> {
                self.res
            }
        }
        impl<'sys> Deref for $ty_name<'sys> {
            type Target = CheckRes<'sys>;
            fn deref(&self) -> &CheckRes<'sys> {
                &self.res
            }
        }
        impl<'sys> DerefMut for $ty_name<'sys> {
            fn deref_mut(&mut self) -> &mut CheckRes<'sys> {
                &mut self.res
            }
        }
        impl<'sys> From<CheckRes<'sys>> for $ty_name<'sys> {
            fn from(res: CheckRes<'sys>) -> $ty_name {
                $ty_name { res }
            }
        }
    )*);
}

wrap! {
    /// Result of a base check, simply wraps a [CheckRes](struct.CheckRes.html).
    BaseRes,
    /// Result of a step check, simply wraps a [CheckRes](struct.CheckRes.html).
    StepRes,
    /// Result of a BMC check, simply wraps a [CheckRes](struct.CheckRes.html).
    BmcRes,
}

impl<'sys> BaseRes<'sys> {
    /// Merges a base result with a step result for BMC.
    ///
    /// The result `res` is such that
    ///
    /// - `okay` contains POs that are in `self.okay ⧵ step.okay`, and
    /// - `cexs` is empty.
    ///
    /// That is, the result only contains POs that
    ///
    /// - hold in the initial states, and
    /// - are not inductive.
    ///
    /// # Errors
    ///
    /// - when the two results mention inconsistent POs.
    pub fn merge_base_with_step(&self, step: &StepRes<'sys>) -> Res<BmcRes<'sys>> {
        macro_rules! abort {
            ($n:expr) => {
                bail!(
                    "asked to merge two inconsistent base/step check results ({})",
                    $n
                )
            };
        }
        let base = self;
        if base.okay.len() + base.cexs.len() != step.okay.len() + step.cexs.len() {
            abort!(format!(
                "{}/{} | {}/{}",
                base.okay.len(),
                base.cexs.len(),
                step.okay.len(),
                step.cexs.len()
            ))
        }

        let mut res = CheckRes {
            okay: base.okay.clone(),
            cexs: Cexs::new(),
        };

        // At this point all POs in `res.okay` are verified in the initial states. Need to remove
        // the POs that are inductive.
        for inductive in &step.okay {
            let was_there = res.okay.remove(inductive);
            if !was_there && !base.cexs.contains_key(inductive) {
                abort!(inductive)
            }
        }

        Ok(res.into())
    }
}

/// Internal mini structure to represent the negation of a borrowed expression.
pub struct NegExpr<'e, E> {
    /// Internal expression reference.
    expr: &'e E,
}
impl<'e, Info, E> Expr2Smt<Info> for NegExpr<'e, E>
where
    E: Expr2Smt<Info>,
{
    fn expr_to_smt2<W: Write>(&self, w: &mut W, i: Info) -> SmtRes<()> {
        write!(w, "(not ")?;
        self.expr.expr_to_smt2(w, i)?;
        write!(w, ")")?;
        Ok(())
    }
}

/// Internal version of a checker.
///
/// Provides low-level features for the actual checker. These features are easy to use wrong, so
/// they are not exposed outside of this crate.
pub struct InternalChecker<'sys> {
    /// Underlying SMT solver.
    solver: Solver,
    /// Transition system.
    sys: &'sys Sys,
    /// List of all variables of the system.
    vars: Vec<Var>,
}
impl<'sys> InternalChecker<'sys> {
    /// Constructor.
    pub fn new(
        sys: &'sys Sys,
        z3_cmd: impl Into<String>,
        tee: Option<impl AsRef<str>>,
    ) -> Res<Self> {
        let z3_cmd = z3_cmd.into();
        let mut split_cmd = z3_cmd.split(|c: char| c.is_whitespace());
        let z3_cmd = split_cmd
            .next()
            .ok_or_else(|| format!("illegal Z3 command `{}`", z3_cmd))?
            .trim();
        let mut conf = SmtConf::z3(z3_cmd);

        for opt in split_cmd {
            let opt = opt.trim();
            if !opt.is_empty() {
                conf.option(opt);
            }
        }

        let mut solver = conf
            .spawn(cexs::SmtParser)
            .chain_err(|| "while spawning z3 solver")?;
        if let Some(path) = tee {
            solver.path_tee(path.as_ref())?
        }
        let vars = sys.decls().all().collect();
        Ok(Self { solver, sys, vars })
    }

    /// Declares all variables for some step.
    pub fn declare_vars(&mut self, step: Unroll) -> Res<()> {
        for var in &self.vars {
            self.solver
                .declare_const_with(var, &var.typ(), step)
                .chain_err(|| format!("while declaring variable `{}@{}`", var, step))?
        }
        Ok(())
    }

    /// Asserts the initial predicate at step `0`.
    pub fn assert_init(&mut self) -> Res<()> {
        self.solver
            .assert_with(self.sys.init(), 0)
            .chain_err(|| "while asserting init predicate at 0")?;
        Ok(())
    }
    /// Asserts the transition predicate at some step.
    #[allow(dead_code)]
    pub fn assert_trans(&mut self, step: Unroll) -> Res<()> {
        self.solver
            .assert_with(self.sys.trans(), step)
            .chain_err(|| format!("while asserting trans predicate at {}", step))?;
        Ok(())
    }

    /// Asserts a stateless expression at some step.
    #[allow(dead_code)]
    pub fn assert_expr(&mut self, expr: &Expr, step: Unroll) -> Res<()> {
        self.solver.assert_with(expr, step).chain_err(|| {
            format!(
                "while asserting stateless expression `{}` at step {}",
                expr, step
            )
        })?;
        Ok(())
    }

    /// Asserts the proof objectives at some step.
    #[allow(dead_code)]
    pub fn assert_po_s(&mut self, step: Unroll, res: &CheckRes) -> Res<()> {
        for (name, po) in self.sys.po_s() {
            if res.okay.contains(name) {
                self.solver.assert_with(&po, step).chain_err(|| {
                    format!("while asserting negation of PO `{}` at step {}", name, step)
                })?
            }
        }
        Ok(())
    }

    /// Asserts the negation of the proof objectives at some step.
    #[allow(dead_code)]
    pub fn assert_not_po_s(&mut self, step: Unroll) -> Res<()> {
        for (name, po) in self.sys.po_s() {
            let not_po = po.negated();
            self.solver.assert_with(&not_po, step).chain_err(|| {
                format!("while asserting negation of PO `{}` at step {}", name, step)
            })?
        }
        Ok(())
    }

    /// Finds falsifications of the proof objectives at some step.
    pub fn find_po_falsifications(&mut self, step: Unroll, res: &mut CheckRes<'sys>) -> Res<bool> {
        let mut changed = false;
        // List of POs to check, the POs in `res.okay`.
        let to_check: Vec<_> = res
            .okay
            .iter()
            .map(|po| {
                self.sys
                    .po_s()
                    .get_key_value(po as &str)
                    .ok_or_else(|| format!("unknown PO `{}`", po))
            })
            .collect();
        for to_check in to_check {
            let (name, po) = to_check?;
            let not_po = po.negated();
            self.solver.push(1)?;
            self.solver.assert_with(&not_po, step).chain_err(|| {
                format!("while asserting negation of PO `{}` at step {}", name, step)
            })?;
            if self.solver.check_sat()? {
                changed = true;
                res.register_falsification(name, &mut self.solver)?
            }
            self.solver.pop(1)?
        }
        Ok(changed)
    }

    /// Checks that the current state of the solver is satisfiable.
    #[allow(dead_code)]
    pub fn check_sat(&mut self) -> Res<bool> {
        let res = self.solver.check_sat()?;
        Ok(res)
    }
}

/// Base (init) checker.
pub struct Base<'sys> {
    /// Underlying checker.
    checker: InternalChecker<'sys>,
}
impl<'sys> Base<'sys> {
    /// Constructor.
    pub fn new(
        sys: &'sys Sys,
        z3_cmd: impl Into<String>,
        tee: Option<impl AsRef<str>>,
    ) -> Res<Self> {
        let tee = tee.map(|s| format!("{}/base.smt2", s.as_ref()));
        Ok(Self {
            checker: InternalChecker::new(sys, z3_cmd, tee)?,
        })
    }

    /// Checks whether some properties are falsified in the initial states.
    pub fn check(&mut self) -> Res<BaseRes<'sys>> {
        self.checker.declare_vars(0)?;
        self.checker.assert_init()?;
        let mut res = CheckRes::new(&self.checker.sys);
        let _ = self.checker.find_po_falsifications(0, &mut res)?;
        Ok(res.into())
    }
}

/// Step (trans) checker.
pub struct Step<'sys> {
    /// Underlying checker.
    checker: InternalChecker<'sys>,
}
impl<'sys> Step<'sys> {
    /// Constructor.
    pub fn new(
        sys: &'sys Sys,
        z3_cmd: impl Into<String>,
        tee: Option<impl AsRef<str>>,
    ) -> Res<Self> {
        let tee = tee.map(|s| format!("{}/step.smt2", s.as_ref()));
        Ok(Self {
            checker: InternalChecker::new(sys, z3_cmd, tee)?,
        })
    }

    /// Checks whether some properties are falsified in the initial states.
    pub fn check(&mut self) -> Res<StepRes<'sys>> {
        self.checker.declare_vars(0)?;
        self.checker.declare_vars(1)?;
        self.checker.assert_trans(0)?;

        let mut res = CheckRes::new(&self.checker.sys);

        'try_to_prove_okay_po_s: loop {
            self.checker.solver.comment(&format!(
                "Pushing scope to try to prove {} PO(s).",
                res.okay.len()
            ))?;
            self.checker.solver.push(1)?;
            self.checker.solver.comment(&format!(
                "Induction hypothesis for {} PO(s).",
                res.okay.len()
            ))?;
            self.checker.assert_po_s(0, &res)?;
            let new_falsifications = self.checker.find_po_falsifications(1, &mut res)?;
            if new_falsifications {
                if res.okay.is_empty() {
                    self.checker
                        .solver
                        .comment("All POs have been falsified, done.")?;
                    self.checker.solver.kill()?;
                    break 'try_to_prove_okay_po_s Ok(res.into());
                } else {
                    self.checker.solver.comment(
                        "New falsification(s) detected, popping and resuming proof attempt.",
                    )?;
                    self.checker.solver.pop(1)?;
                    continue 'try_to_prove_okay_po_s;
                }
            } else {
                self.checker
                    .solver
                    .comment("Successfully proved remaining PO(s), done.")?;
                self.checker.solver.kill()?;
                break 'try_to_prove_okay_po_s Ok(res.into());
            }
        }
    }
}

/// Bounded Model Checker.
pub struct Bmc<'sys> {
    /// Underlying checker.
    checker: InternalChecker<'sys>,
    /// Next step at which the system should be unrolled.
    ///
    /// When `self.next_step` is `s`, it means the system is currently unrolled to `s - 1`.
    ///
    /// # Invariants
    ///
    /// - `self.next_step > 0`
    next_step: Unroll,
    /// Step at which the system was last check.
    ///
    /// # Invariants
    ///
    /// - `self.check_step == self.next_step || self.check_step + 1 == self.next_step`
    check_step: Unroll,
    /// Bmc result.
    res: BmcRes<'sys>,
}
impl<'sys> Bmc<'sys> {
    /// Constructor.
    pub fn new(
        sys: &'sys Sys,
        z3_cmd: impl Into<String>,
        tee: Option<impl AsRef<str>>,
        res: BmcRes<'sys>,
    ) -> Res<Self> {
        let tee = tee.map(|s| format!("{}/bmc.smt2", s.as_ref()));

        let mut checker = InternalChecker::new(sys, z3_cmd, tee)?;
        checker.declare_vars(0)?;
        checker.assert_init()?;
        Ok(Self {
            checker,
            next_step: 1,
            check_step: 0,
            res,
        })
    }

    /// Accessor to the BMC result.
    pub fn res(&self) -> &BmcRes<'sys> {
        &self.res
    }

    /// True if all POs have been falsified.
    pub fn is_done(&self) -> bool {
        self.res.all_falsified()
    }

    /// The next step to check.
    pub fn next_check_step(&self) -> Unroll {
        self.check_step
    }

    /// Destroys itself to yield the result.
    pub fn destroy(mut self) -> Res<BmcRes<'sys>> {
        self.checker
            .solver
            .kill()
            .chain_err(|| "while killing the BMC solver")?;
        Ok(self.res)
    }

    /// Unrolls the system and performs the next check.
    pub fn next_check(&mut self) -> Res<bool> {
        let res = if self.check_step == 0 {
            self.check()
                .chain_err(|| "while checking for a falsification in the initial state(s)")?
        } else {
            let step = self.next_step;
            self.unroll()
                .chain_err(|| format!("while unrolling the system to step {}", step))?;
            self.check().chain_err(|| {
                format!(
                    "while checking for a falsification at step {}",
                    self.check_step
                )
            })?
        };
        Ok(res)
    }

    /// Checks whether some properties can be falsified at the current step.
    ///
    /// Returns `true` if some new falsifications were discovered.
    fn check(&mut self) -> Res<bool> {
        if !self.next_step == self.check_step + 1 {
            bail!(
                "illegal configuration for a BMC check, next step is {} but check step is {}",
                self.next_step,
                self.check_step
            )
        }
        let res = self
            .checker
            .find_po_falsifications(self.check_step, &mut self.res);
        self.check_step += 1;
        res
    }

    /// Unrolls the system one step further.
    fn unroll(&mut self) -> Res<()> {
        if !self.next_step == self.check_step || self.next_step < 1 {
            bail!(
                "illegal configuration for a BMC unroll, next step is {} but check step is {}",
                self.next_step,
                self.check_step
            )
        }
        debug_assert!(self.next_step > 0);
        self.checker.declare_vars(self.next_step)?;
        let res = self.checker.assert_trans(self.next_step - 1);
        self.next_step += 1;
        res
    }
}
