//! Provides parser-equipped [`rsmt2::Solver`]s.

prelude!(expr::*, parse::Parser);

/// SMT-LIB parser for *unrolled* expressions, idents, types...
#[derive(Debug, Clone, Copy)]
pub struct StatefulParser;

impl<'a> rsmt2::parse::IdentParser<(String, Option<Unroll>), Typ, &'a str> for StatefulParser {
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
    > for StatefulParser
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

/// SMT-LIB parser for *unrolled* expressions, idents, types...
#[derive(Debug, Clone, Copy)]
pub struct StatelessParser;

impl<'a> rsmt2::parse::IdentParser<String, Typ, &'a str> for StatelessParser {
    fn parse_ident(self, input: &'a str) -> SmtRes<String> {
        let input = input.trim();
        Ok(input.into())
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
impl<'a, Br: std::io::BufRead> rsmt2::parse::ModelParser<String, Typ, Cst, &'a mut RSmtParser<Br>>
    for StatelessParser
{
    fn parse_value(
        self,
        input: &'a mut RSmtParser<Br>,
        _: &String,
        _: &[(String, Typ)],
        _: &Typ,
    ) -> SmtRes<Cst> {
        let sexpr = input.get_sexpr()?;
        let mut parser = Parser::new(sexpr);
        if let Ok(Some(cst)) = parser.try_cst() {
            Ok(cst)
        } else {
            Err(format!("expected constant, got `{}`", sexpr).into())
        }
    }
}

/// Wrapper for rsmt2's solver equipped with one of our parser.
pub struct Solver<P> {
    solver: SmtSolver<P>,
}
/// Stateful solver, can parse stateful variables.
pub type SFSolver = Solver<StatefulParser>;
/// Stateless solver, sees all variables as stateless.
pub type SLSolver = Solver<StatelessParser>;

impl<P> Solver<P> {
    /// Constructor.
    pub fn new_with(mut conf: SmtConf, parser: P, tee: Option<PathBuf>) -> Res<Self> {
        conf.check_success();

        let mut solver = conf
            .spawn(parser)
            .chain_err(|| "while spawning z3 solver")?;
        if let Some(path) = tee {
            solver.path_tee(path)?
        }
        Ok(Self { solver })
    }
}
impl SFSolver {
    /// Stateful solver constructor.
    pub fn new(conf: SmtConf, tee: Option<PathBuf>) -> Res<Self> {
        Self::new_with(conf, StatefulParser, tee)
    }
}
impl SLSolver {
    /// Stateless solver constructor.
    pub fn new(conf: SmtConf, tee: Option<PathBuf>) -> Res<Self> {
        Self::new_with(conf, StatelessParser, tee)
    }
}
impl<P> Deref for Solver<P> {
    type Target = SmtSolver<P>;
    fn deref(&self) -> &Self::Target {
        &self.solver
    }
}
impl<P> DerefMut for Solver<P> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.solver
    }
}
