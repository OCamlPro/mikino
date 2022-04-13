//! Counterexample extraction.

crate::prelude!();

use expr::{Cst, Typ, Var};
use parse::Parser;

/// A counterexample.
#[derive(Debug, Clone)]
pub struct Cex {
    /// Trace of values for each variable, organized by steps.
    pub trace: Map<Unroll, Map<Var, Cst>>,
    /// Unexpected variables produced by Z3.
    ///
    /// Z3 can produce additional variables when asked for a model. This can happen when there is a
    /// potential division by zero for instance.
    pub unexpected: Map<String, String>,
}
impl Cex {
    /// Constructor.
    pub fn new() -> Self {
        Self {
            trace: Map::new(),
            unexpected: Map::new(),
        }
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

    /// Inserts a value for an unexpected variable.
    pub fn insert_unexpected(&mut self, var: impl Into<String>, cst: impl Into<String>) -> Res<()> {
        let var = var.into();
        let prev = self.unexpected.insert(var.clone(), cst.into());
        if prev.is_some() {
            bail!("trying to insert a value for for {} twice", var)
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
            match (cst, step) {
                (Either::Left(cst), Some(step)) => {
                    assert!(args.is_empty());
                    let var = Var::new(var_id, typ);
                    self.insert(step, var, cst)?;
                }
                (cst, step) => {
                    let cst = cst.map_left(|c| c.to_string()).into_inner();
                    let mut desc = var_id;
                    if let Some(step) = step {
                        desc.push_str(&format!("@{}", step));
                    };
                    if !args.is_empty() {
                        desc.push_str(" (");
                        for (idx, ((arg, _), typ)) in args.into_iter().enumerate() {
                            if idx > 0 {
                                desc.push(' ');
                            }
                            desc.push_str(&format!("({} {})", arg, typ));
                        }
                        desc.push(')');
                    }
                    desc.push_str(&format!(" {}", typ));
                    self.insert_unexpected(desc, cst)?;
                }
            }
            // if let Some(step) = step {
            // } else {
            //     let mut desc = var_id;
            //     self.insert_unexpected(desc, cst)?
            // }
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

/// SMT-LIB parser for expressions, idents, types...
#[derive(Debug, Clone, Copy)]
pub struct SmtParser;
impl<'a> rsmt2::parse::IdentParser<(String, Option<Unroll>), Typ, &'a str> for SmtParser {
    fn parse_ident(self, input: &'a str) -> SmtRes<(String, Option<Unroll>)> {
        let input = input.trim();
        let subs = input.split('@');
        let mut subs = subs.into_iter();
        let name = subs
            .next()
            .ok_or_else(|| format!("unexpected model variable `{}`", input))?;
        let step = if let Some(Ok(step)) = subs.next().map(|s| usize::from_str_radix(s, 10)) {
            Some(step)
        } else {
            None
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
impl<'a, Br: std::io::BufRead>
    rsmt2::parse::ModelParser<
        (String, Option<Unroll>),
        Typ,
        Either<Cst, String>,
        &'a mut RSmtParser<Br>,
    > for SmtParser
{
    fn parse_value(
        self,
        input: &'a mut RSmtParser<Br>,
        _: &(String, Option<Unroll>),
        _: &[((String, Option<Unroll>), Typ)],
        _: &Typ,
    ) -> SmtRes<Either<Cst, String>> {
        let sexpr = input.get_sexpr()?;
        let mut parser = Parser::new(sexpr);
        if let Ok(Some(cst)) = parser.try_cst() {
            Ok(Either::Left(cst))
        } else {
            Ok(Either::Right(sexpr.into()))
        }
    }
}
