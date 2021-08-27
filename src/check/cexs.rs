//! Counterexample extraction.

crate::prelude!();

use expr::{Cst, Typ, Var};
use parse::Parser;
use rsmt2::{SmtRes, Solver as SmtSolver};

/// A counterexample.
#[derive(Debug, Clone)]
pub struct Cex {
    /// Trace of values for each variable, organized by steps.
    pub trace: Map<Unroll, Map<Var, Cst>>,
}
impl Cex {
    /// Constructor.
    pub fn new() -> Self {
        Self { trace: Map::new() }
    }

    /// Inserts a value for a variable at some step.
    pub fn insert(&mut self, step: Unroll, var: Var, cst: Cst) -> Res<()> {
        let var_id = var.id().to_string();
        let prev = self
            .trace
            .entry(step)
            .or_insert_with(Map::new)
            .insert(var, cst);
        if prev.is_some() {
            bail!(
                "trying to insert a value for {}@{} twice while constructing cex",
                var_id,
                step
            )
        } else {
            Ok(())
        }
    }

    /// Populates itself given a solver.
    ///
    /// Uses `get_model` to retrieve the counterexample. The solver must have answered `sat` to a PO
    /// falsification query right before it is passed to this function.
    pub fn populate(&mut self, solver: &mut Solver) -> Res<()> {
        let model = solver.get_model().chain_err(|| "while retrieving cex")?;
        for ((var_id, step), args, typ, cst) in model {
            debug_assert!(args.is_empty());
            let var = Var::new(var_id, typ);
            self.insert(step, var, cst)?
        }
        Ok(())
    }
}

/// Counterexamples for some POs.
#[derive(Debug, Clone)]
pub struct Cexs<'sys> {
    /// Map from POs to a counterexample for this PO.
    pub falsifications: Map<&'sys String, Cex>,
}
impl<'sys> Deref for Cexs<'sys> {
    type Target = Map<&'sys String, Cex>;
    fn deref(&self) -> &Map<&'sys String, Cex> {
        &self.falsifications
    }
}
impl<'sys> DerefMut for Cexs<'sys> {
    fn deref_mut(&mut self) -> &mut Map<&'sys String, Cex> {
        &mut self.falsifications
    }
}
impl<'sys> Cexs<'sys> {
    /// Constructor.
    pub fn new() -> Self {
        Self {
            falsifications: Map::new(),
        }
    }
    /// Inserts a falsification for a PO.
    ///
    /// # Errors
    ///
    /// - when a counterexample for `po` is already registered.
    pub fn insert_falsification(&mut self, po: &'sys String, solver: &mut Solver) -> Res<()> {
        let mut cex = Cex::new();
        cex.populate(solver)?;
        let prev = self.insert(po, cex);
        if prev.is_some() {
            bail!(
                "trying to register more than one falsification of PO `{}`",
                po
            )
        }
        Ok(())
    }

    /// True if there are no falsifications.
    pub fn is_empty(&self) -> bool {
        self.falsifications.is_empty()
    }
}

/// Type alias for rsmt2's solver equipped with our parser.
pub type Solver = SmtSolver<SmtParser>;

#[derive(Debug, Clone, Copy)]
pub struct SmtParser;
impl<'a> rsmt2::parse::IdentParser<(String, Unroll), Typ, &'a str> for SmtParser {
    fn parse_ident(self, input: &'a str) -> SmtRes<(String, Unroll)> {
        let input = input.trim();
        let subs = input.split('@');
        let mut subs = subs.into_iter();
        let name = subs
            .next()
            .ok_or_else(|| format!("unexpected model variable `{}`", input))?;
        let step = if let Some(Ok(step)) = subs.next().map(|s| usize::from_str_radix(s, 10)) {
            step
        } else {
            bail!("unexpected model variable `{}`", input)
        };
        Ok((name.into(), step))
    }
    fn parse_type(self, input: &'a str) -> SmtRes<Typ> {
        match input {
            "Bool" => Ok(Typ::Bool),
            "Int" => Ok(Typ::Int),
            "Real" => Ok(Typ::Rat),
            _ => bail!("unexpected type string `{}`", input),
        }
    }
}
impl<'a> rsmt2::parse::ModelParser<(String, Unroll), Typ, Cst, &'a str> for SmtParser {
    fn parse_value(
        self,
        input: &'a str,
        _: &(String, Unroll),
        _: &[((String, Unroll), Typ)],
        _: &Typ,
    ) -> SmtRes<Cst> {
        let mut parser = Parser::new(input);
        if let Ok(Some(cst)) = parser.try_cst() {
            Ok(cst)
        } else {
            bail!("unexpected value string `{}`", input)
        }
    }
}
