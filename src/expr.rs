//! Defines the expression structure used to represent predicates.

crate::prelude!();

use rsmt2::print::{Expr2Smt, Sort2Smt, Sym2Smt};

#[cfg(test)]
mod test;

pub use crate::{build_expr as build, build_typ};

/// A type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Typ {
    /// Bool type.
    Bool,
    /// Integer type.
    Int,
    /// Rational type.
    Rat,
}
impl Typ {
    /// Creates a bool type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::Typ;
    /// let bool_typ = Typ::bool();
    /// assert_eq!(&bool_typ.to_string(), "bool")
    /// ```
    pub fn bool() -> Self {
        Self::Bool
    }
    /// Creates an integer type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::Typ;
    /// let int_typ = Typ::int();
    /// assert_eq!(&int_typ.to_string(), "int")
    /// ```
    pub fn int() -> Self {
        Self::Int
    }
    /// Creates a rational type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::Typ;
    /// let rat_typ = Typ::rat();
    /// assert_eq!(&rat_typ.to_string(), "rat")
    /// ```
    pub fn rat() -> Self {
        Self::Rat
    }

    /// True if the type is an arithmetic one.
    pub fn is_arith(self) -> bool {
        match self {
            Self::Bool => false,
            Self::Int | Self::Rat => true,
        }
    }
}
impl Sort2Smt for Typ {
    fn sort_to_smt2<W: Write>(&self, w: &mut W) -> SmtRes<()> {
        write!(
            w,
            "{}",
            match self {
                Self::Bool => "Bool",
                Self::Int => "Int",
                Self::Rat => "Real",
            }
        )?;
        Ok(())
    }
}

/// Operator precedence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Precedence {
    /// Maximal precedence.
    Max,
    /// Numeric precedence.
    Some(usize),
}
impl Precedence {
    /// Constructor.
    pub const fn new(precedence: usize) -> Self {
        Self::Some(precedence)
    }
    /// Maximal precedence.
    pub const fn max() -> Self {
        Self::Max
    }
}
impl PartialOrd for Precedence {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering::*;
        match self {
            Self::Max => {
                if *other == Self::Max {
                    Some(Equal)
                } else {
                    Some(Greater)
                }
            }
            Self::Some(self_prec) => match other {
                Self::Max => Some(Less),
                Self::Some(other_prec) => self_prec.partial_cmp(other_prec),
            },
        }
    }
}

/// Constants.
///
/// Currently only booleans, integers and rationals are supported.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Cst {
    /// Bool constant.
    B(bool),
    /// Integer constant.
    I(Int),
    /// Rational constant.
    R(Rat),
}
impl HasTyp for Cst {
    fn typ(&self) -> Typ {
        match self {
            Self::B(_) => Typ::Bool,
            Self::I(_) => Typ::Int,
            Self::R(_) => Typ::Rat,
        }
    }
}
impl Cst {
    /// Creates a boolean constant.
    pub fn bool(b: bool) -> Self {
        Cst::B(b)
    }
    /// Creates an integer constant.
    pub fn int<I: Into<Int>>(i: I) -> Self {
        Cst::I(i.into())
    }
    /// Creates a rational constant.
    pub fn rat<R: Into<Rat>>(r: R) -> Self {
        Cst::R(r.into())
    }
}
impl Expr2Smt<()> for Cst {
    fn expr_to_smt2<W: Write>(&self, w: &mut W, _: ()) -> SmtRes<()> {
        match self {
            Self::B(b) => write!(w, "{}", b)?,
            Self::I(i) => write!(w, "{}", i)?,
            Self::R(r) => write!(w, "(/ {} {})", r.numer(), r.denom())?,
        }
        Ok(())
    }
}

/// Operator in/pre/suffix.
#[derive(Debug, Clone, Copy)]
pub enum Fix {
    In,
    Pre,
    Suf,
}

/// Operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Op {
    Ite,
    Implies,
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Ge,
    Le,
    Gt,
    Lt,
    Eq,
    Not,
    And,
    Or,
}
impl Op {
    /// Tries to parse an operator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::Op;
    /// assert_eq!(Op::of_str("+"), Some(Op::Add));
    /// assert_eq!(Op::of_str("and"), Some(Op::And));
    /// assert_eq!(Op::of_str("⋀"), Some(Op::And));
    /// assert_eq!(Op::of_str("add"), None);
    /// ```
    pub fn of_str<Str: AsRef<str>>(s: Str) -> Option<Self> {
        use Op::*;
        let res = match s.as_ref() {
            "ite" => Ite,
            "=>" | "implies" | "⇒" => Implies,
            "+" => Add,
            "-" => Sub,
            "*" => Mul,
            "/" => Div,
            "div" => IDiv,
            "mod" => Mod,
            ">=" | "≥" => Ge,
            "<=" | "≤" => Le,
            ">" => Gt,
            "<" => Lt,
            "=" => Eq,
            "not" | "!" | "¬" => Not,
            "and" | "&&" | "⋀" => And,
            "or" | "||" | "⋁" => Or,
            _ => return None,
        };
        Some(res)
    }

    /// Human-SMT string representation.
    pub fn hsmt_str(self) -> &'static [&'static str] {
        match self {
            Self::Ite => &["if", "then", "else"],
            Self::Implies => &["⇒"],
            Self::Add => &["+"],
            Self::Sub => &["-"],
            Self::Mul => &["*"],
            Self::Div => &["/"],
            Self::IDiv => &["/"],
            Self::Mod => &["%"],
            Self::Ge => &["≥"],
            Self::Le => &["≤"],
            Self::Gt => &[">"],
            Self::Lt => &["<"],
            Self::Eq => &["="],
            Self::Not => &["¬"],
            Self::And => &["⋀"],
            Self::Or => &["⋁"],
        }
    }

    /// Human-SMT string representation.
    pub fn smt_str(self) -> &'static str {
        match self {
            Self::Ite => "ite",
            Self::Implies => "=>",
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::IDiv => "/",
            Self::Mod => "%",
            Self::Ge => "≥",
            Self::Le => "≤",
            Self::Gt => ">",
            Self::Lt => "<",
            Self::Eq => "=",
            Self::Not => "¬",
            Self::And => "⋀",
            Self::Or => "⋁",
        }
    }

    /// True if `self` is an arithmetic relation.
    pub fn is_arith_relation(self) -> bool {
        match self {
            Self::Ge | Self::Le | Self::Gt | Self::Lt => true,
            Self::Ite
            | Self::Implies
            | Self::Add
            | Self::Sub
            | Self::Mul
            | Self::Div
            | Self::IDiv
            | Self::Mod
            | Self::Eq
            | Self::Not
            | Self::And
            | Self::Or => false,
        }
    }

    /// Minimal arity of `self`.
    pub fn min_arity(self) -> usize {
        match self {
            Self::Not | Self::Add | Self::Sub => 1,
            Self::Mod
            | Self::Mul
            | Self::Div
            | Self::IDiv
            | Self::And
            | Self::Or
            | Self::Implies
            | Self::Eq
            | Self::Le
            | Self::Lt
            | Self::Ge
            | Self::Gt => 2,
            Self::Ite => 3,
        }
    }

    /// Maximal arity for `self`, `None` if infinite.
    pub fn max_arity(self) -> Option<usize> {
        match self {
            Self::Not => Some(1),
            Self::Add
            | Self::Sub
            | Self::Mul
            | Self::And
            | Self::Or
            | Self::Implies
            | Self::Eq
            | Self::Le
            | Self::Lt
            | Self::Ge
            | Self::Gt => None,
            Self::Mod | Self::Div | Self::IDiv => Some(2),
            Self::Ite => Some(3),
        }
    }

    /// True if the operator is left associative.
    pub fn is_left_associative(self) -> bool {
        match self {
            Self::Add
            | Self::Sub
            | Self::Mul
            | Self::And
            | Self::Or
            | Self::Implies
            | Self::Eq
            | Self::Le
            | Self::Lt
            | Self::Ge
            | Self::Gt => true,
            Self::Not | Self::Mod | Self::Div | Self::IDiv | Self::Ite => false,
        }
    }

    /// Type-checks an operator application.
    pub fn type_check<V: HasTyp>(self, args: &[PExpr<V>]) -> Res<Typ> {
        if args.len() < self.min_arity() {
            bail!(
                "`{}` expects at least {} argument(s)",
                self,
                self.min_arity(),
            )
        }
        if let Some(max) = self.max_arity() {
            if args.len() > max {
                bail!("`{}` expects at most {} argument(s)", self, max)
            }
        }

        let typ = match self {
            Self::Ite => {
                let typ = args[0].typ();
                if typ != Typ::Bool {
                    bail!("expected first argument of type `bool`, got `{}`", typ)
                }

                let thn_typ = args[1].typ();
                let els_typ = args[2].typ();

                if thn_typ != els_typ {
                    bail!(
                        "`{}`'s second and third arguments should have the same type, got `{}` and `{}`",
                        self, thn_typ, els_typ,
                    )
                }

                thn_typ
            }
            Self::Implies | Self::And | Self::Or | Self::Not => {
                if args.iter().any(|e| e.typ() != Typ::Bool) {
                    bail!("`{}`'s arguments must all be boolean expressions", self)
                }
                Typ::Bool
            }

            Self::Add
            | Self::Sub
            | Self::Mul
            | Self::Div
            | Self::IDiv
            | Self::Mod
            | Self::Le
            | Self::Ge
            | Self::Lt
            | Self::Gt => {
                let mut typs = args.iter().map(PExpr::typ);
                let first = typs.next().expect("at least one argument");
                if !first.is_arith() {
                    bail!(
                        "`{}`'s arguments must have an arithmetic type, unexpected type `{}`",
                        self,
                        first,
                    )
                }
                for typ in typs {
                    if typ != first {
                        bail!(
                            "`{}`'s arguments must all have the same type, found `{}` and `{}`",
                            self,
                            first,
                            typ,
                        )
                    }
                }
                if (self == Self::IDiv || self == Self::Mod) && first != Typ::Int {
                    bail!(
                        "`{}` can only be applied to integer arguments, found `{}`",
                        self,
                        first,
                    )
                }

                if self == Self::Div {
                    Typ::Rat
                } else if self == Self::Mod {
                    Typ::Int
                } else if self.is_arith_relation() {
                    Typ::Bool
                } else {
                    first
                }
            }

            Self::Eq => {
                let mut typs = args.iter().map(PExpr::typ);
                let first = typs.next().unwrap();
                for typ in typs {
                    if typ != first {
                        bail!(
                            "`{}`'s arguments must all have the same type, found `{}` and `{}`",
                            self,
                            first,
                            typ,
                        )
                    }
                }
                Typ::Bool
            }
        };

        Ok(typ)
    }
}
impl Expr2Smt<()> for Op {
    fn expr_to_smt2<W: Write>(&self, w: &mut W, _: ()) -> SmtRes<()> {
        write!(
            w,
            "{}",
            match self {
                Self::Ite => "ite",
                Self::Implies => "=>",
                Self::Add => "+",
                Self::Sub => "-",
                Self::Mul => "*",
                Self::Div => "/",
                Self::IDiv => "div",
                Self::Mod => "mod",
                Self::Ge => ">=",
                Self::Le => "<=",
                Self::Gt => ">",
                Self::Lt => "<",
                Self::Eq => "=",
                Self::Not => "not",
                Self::And => "and",
                Self::Or => "or",
            }
        )?;
        Ok(())
    }
}

/// Trait implemented by all variables.
pub trait HasTyp: fmt::Display {
    /// Type accessor.
    fn typ(&self) -> Typ;
}

/// A stateless variable.
///
/// This type of variable is used in stateless expressions.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var {
    /// Variable identifier.
    id: String,
    /// Type of the variable.
    typ: Typ,
}
impl Var {
    /// Constructor.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::{Var, Typ};
    /// # #[allow(dead_code)]
    /// let var = Var::new("v_1", Typ::Bool);
    /// ```
    pub fn new<S: Into<String>>(id: S, typ: Typ) -> Self {
        Self { id: id.into(), typ }
    }

    /// Identifier accessor.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::{Var, Typ};
    /// let var = Var::new("v_1", Typ::Bool);
    /// assert_eq!(var.id(), "v_1");
    /// ```
    pub fn id(&self) -> &str {
        &self.id
    }
}
impl HasTyp for Var {
    /// Type accessor.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::{Var, Typ, HasTyp};
    /// let var = Var::new("v_1", Typ::Bool);
    /// assert_eq!(var.typ(), Typ::Bool);
    /// ```
    fn typ(&self) -> Typ {
        self.typ
    }
}
impl Sym2Smt<Unroll> for Var {
    fn sym_to_smt2<W: Write>(&self, w: &mut W, step: Unroll) -> SmtRes<()> {
        write!(w, "{}@{}", self.id, step)?;
        Ok(())
    }
}

/// A stateful variable.
///
/// This type of variable is used in stateful expressions: expressions that span over two steps.
/// Typically, the transition relation of a system is stateful. A stateful variable is essentially a
/// [Var] with a *next* flag that specifies whether the stateful variable refers to the current or
/// next version of the underlying variable.
///
/// [Var]: struct.Var.html
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SVar {
    /// Underlying variable.
    var: Var,
    /// True if the variable refers to the next state version of the variable.
    nxt: bool,
}
impl SVar {
    /// State variable constructor with a `next` flag.
    pub fn new(var: Var, nxt: bool) -> Self {
        Self { var, nxt }
    }
    /// Constructor for next state variables.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::{Var, SVar, Typ, HasTyp};
    /// let var = Var::new("v_1", Typ::Bool);
    /// let svar = SVar::new_next(var);
    /// assert_eq!(&svar.to_string(), "v_1@1");
    /// assert_eq!(svar.id(), "v_1");
    /// assert_eq!(svar.typ(), Typ::Bool);
    /// ```
    pub fn new_next(var: Var) -> Self {
        Self::new(var, true)
    }

    /// Constructor for current state variables.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::{Var, SVar, Typ, HasTyp};
    /// let var = Var::new("v_1", Typ::Bool);
    /// let svar = SVar::new_curr(var);
    /// assert_eq!(&svar.to_string(), "v_1@0");
    /// assert_eq!(svar.id(), "v_1");
    /// assert_eq!(svar.typ(), Typ::Bool);
    /// ```
    pub fn new_curr(var: Var) -> Self {
        Self::new(var, false)
    }

    /// True if the state variable is a next state variable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::{Var, SVar, Typ};
    /// let var = Var::new("v_1", Typ::Bool);
    /// let svar = SVar::new_next(var.clone());
    /// assert!(svar.is_next());
    /// let svar = SVar::new_curr(var);
    /// assert!(!svar.is_next());
    /// ```
    pub fn is_next(&self) -> bool {
        self.nxt
    }
}
impl Sym2Smt<Unroll> for SVar {
    fn sym_to_smt2<W: Write>(&self, w: &mut W, step: Unroll) -> SmtRes<()> {
        write!(w, "{}@{}", self.id, if self.nxt { step + 1 } else { step })?;
        Ok(())
    }
}
impl HasTyp for SVar {
    fn typ(&self) -> Typ {
        self.typ
    }
}

/// The polymorphic expression structure.
///
/// This structure is polymorphic in the type of variables. This allows to create two types, [Expr]
/// and [SExpr] for stateless and stateful expressions respectively. The former is `PExpr<Var>`
/// while the latter is `PExpr<SVar>`.
///
/// [Expr]: type.Expr.html
/// [SExpr]: type.SExpr.html
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PExpr<V> {
    /// A constant.
    Cst(Cst),
    /// A variable.
    Var(V),
    /// An operator application.
    App {
        /// The operator.
        op: Op,
        /// The arguments.
        args: Vec<PExpr<V>>,
    },
}
impl<V> PExpr<V> {
    /// Variable constructor.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::{PExpr, Var, SVar, Typ};
    /// let var = Var::new("v_1", Typ::Bool);
    /// let expr: PExpr<Var> = PExpr::new_var(var.clone());
    /// assert_eq!(expr, PExpr::Var(var.clone()));
    /// let svar = SVar::new_next(var);
    /// let expr: PExpr<SVar> = PExpr::new_var(svar.clone());
    /// assert_eq!(expr, PExpr::Var(svar));
    /// ```
    pub fn new_var(var: V) -> Self {
        Self::Var(var)
    }

    /// Constant constructor.
    pub fn new_cst(cst: Cst) -> Self {
        Self::Cst(cst)
    }

    /// Operator application constructor.
    /// Variable constructor.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::expr::{PExpr, Var, SVar, Typ, Op};
    /// let var = Var::new("v_1", Typ::Bool);
    /// let expr: PExpr<Var> = PExpr::new_var(var.clone());
    /// assert_eq!(expr, PExpr::Var(var.clone()));
    /// let svar = SVar::new_next(var);
    /// let expr: PExpr<SVar> = PExpr::new_var(svar.clone());
    /// assert_eq!(expr, PExpr::Var(svar));
    /// ```
    pub fn new_op(op: Op, args: Vec<Self>) -> Res<Self>
    where
        V: HasTyp,
    {
        op.type_check(&args)?;
        Ok(Self::simplify_app(op, args))
    }

    /// Simplifies the application of `op` to `args`, **non-recursively**.
    fn simplify_app(op: Op, args: Vec<Self>) -> Self {
        match (op, args.len()) {
            (Op::Sub, 1) if args[0].is_cst() => match &args[0] {
                Self::Cst(Cst::I(i)) => Cst::I(-i).into(),
                Self::Cst(Cst::R(r)) => Cst::R(-r).into(),
                Self::Cst(Cst::B(_)) => panic!("trying to apply `{}` to a boolean", op),
                _ => Self::App { op, args },
            },
            (Op::Div, 2) if args[0].is_cst() && args[1].is_cst() => match (&args[0], &args[1]) {
                (Self::Cst(Cst::I(lft)), Self::Cst(Cst::I(rgt))) => Cst::I(lft - rgt).into(),
                (Self::Cst(Cst::R(lft)), Self::Cst(Cst::R(rgt))) => Cst::R(lft - rgt).into(),
                _ => panic!("trying to apply `{}` to arguments of unexpected type", op),
            },
            _ => Self::App { op, args },
        }
    }

    /// True if `self` is a constant.
    pub fn is_cst(&self) -> bool {
        match self {
            Self::Cst(_) => true,
            Self::Var(_) | Self::App { .. } => false,
        }
    }
    /// True if `self` is a variable.
    pub fn is_var(&self) -> bool {
        match self {
            Self::Var(_) => true,
            Self::Cst(_) | Self::App { .. } => false,
        }
    }
    /// True if `self` is an application.
    pub fn is_app(&self) -> bool {
        match self {
            Self::App { .. } => true,
            Self::Cst(_) | Self::Var(_) => false,
        }
    }

    /// Negation of a reference to an expression.
    ///
    /// This is mostly useful in cases when we have a reference to an expression we don't want to
    /// clone, and want to assert the negation.
    pub fn negated(&self) -> NotPExpr<V> {
        self.into()
    }
}
impl<V: HasTyp> HasTyp for PExpr<V> {
    fn typ(&self) -> Typ {
        match self {
            Self::Var(var) => var.typ(),
            Self::Cst(cst) => cst.typ(),
            Self::App { op, args } => match op.type_check(args) {
                Ok(typ) => typ,
                Err(e) => panic!("illegal operator application `{}`: {}", self, e),
            },
        }
    }
}
impl<Info: Copy, V: Sym2Smt<Info>> Expr2Smt<Info> for PExpr<V> {
    fn expr_to_smt2<W: Write>(&self, w: &mut W, i: Info) -> SmtRes<()> {
        match self {
            Self::Cst(cst) => cst.expr_to_smt2(w, ()),
            Self::Var(var) => var.sym_to_smt2(w, i),
            Self::App { op, args } => {
                write!(w, "(")?;
                op.expr_to_smt2(w, ())?;
                for arg in args {
                    write!(w, " ")?;
                    arg.expr_to_smt2(w, i)?
                }
                write!(w, ")")?;
                Ok(())
            }
        }
    }
}

/// A simple (stateless) expression.
pub type Expr = PExpr<Var>;

/// A stateful expression.
pub type SExpr = PExpr<SVar>;

/// Represents the negation of a borrowed expression.
///
/// This is mostly useful in cases when we have a reference to an expression we don't want to clone,
/// and want to assert the negation.
///
/// # Examples
///
/// ```rust
/// # use mikino_api::expr::{self, NotPExpr, Expr, Var};
/// use mikino_api::rsmt2::print::Expr2Smt;
/// let expr = expr::build!(
///     (and (>= (v_1: int) 0) (v_2: bool))
/// );
/// let expr = &expr;
///
/// let not_expr: NotPExpr<Var> = expr.negated();
///
/// use std::io::Write;
/// let mut buff = vec![];
/// not_expr.expr_to_smt2(&mut buff, 0);
/// let s = String::from_utf8_lossy(&buff);
/// assert_eq!(&s, "(not (and (>= v_1@0 0) v_2@0))")
/// ```
pub struct NotPExpr<'a, V> {
    expr: &'a PExpr<V>,
}
impl<'a, V> From<&'a PExpr<V>> for NotPExpr<'a, V> {
    fn from(expr: &'a PExpr<V>) -> Self {
        Self { expr }
    }
}
impl<'a, Info: Copy, V: Sym2Smt<Info>> Expr2Smt<Info> for NotPExpr<'a, V> {
    fn expr_to_smt2<W: Write>(&self, w: &mut W, i: Info) -> SmtRes<()> {
        write!(w, "(not ")?;
        self.expr.expr_to_smt2(w, i)?;
        write!(w, ")")?;
        Ok(())
    }
}

/// Packs basic trait implementations.
mod trait_impls {
    use super::*;

    impl fmt::Display for Typ {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Self::Bool => write!(fmt, "bool"),
                Self::Int => write!(fmt, "int"),
                Self::Rat => write!(fmt, "rat"),
            }
        }
    }

    impl fmt::Display for Op {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Self::Ite => write!(fmt, "ite"),
                Self::Implies => write!(fmt, "=>"),
                Self::Add => write!(fmt, "+"),
                Self::Sub => write!(fmt, "-"),
                Self::Mul => write!(fmt, "*"),
                Self::Div => write!(fmt, "/"),
                Self::IDiv => write!(fmt, "div"),
                Self::Mod => write!(fmt, "%"),
                Self::Ge => write!(fmt, ">="),
                Self::Le => write!(fmt, "<="),
                Self::Gt => write!(fmt, ">"),
                Self::Lt => write!(fmt, "<"),
                Self::Eq => write!(fmt, "="),
                Self::Not => write!(fmt, "not"),
                Self::And => write!(fmt, "and"),
                Self::Or => write!(fmt, "or"),
            }
        }
    }

    impl fmt::Display for Cst {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Self::B(b) => b.fmt(fmt),
                Self::I(i) => {
                    if i.sign() == Sign::Minus {
                        write!(fmt, "(- {})", -i)
                    } else {
                        i.fmt(fmt)
                    }
                }
                Self::R(r) => {
                    let (num, den) = (r.numer(), r.denom());
                    match (num.sign(), den.sign()) {
                        (Sign::Minus, Sign::Minus) => write!(fmt, "(/ {} {})", -num, -den),
                        (Sign::Minus, _) => write!(fmt, "(- (/ {} {}))", -num, den),
                        (_, Sign::Minus) => write!(fmt, "(- (/ {} {}))", num, -den),
                        _ => write!(fmt, "(/ {} {})", num, den),
                    }
                }
            }
        }
    }
    impl From<bool> for Cst {
        fn from(b: bool) -> Self {
            Self::B(b)
        }
    }
    impl From<Int> for Cst {
        fn from(i: Int) -> Self {
            Self::I(i)
        }
    }
    impl From<usize> for Cst {
        fn from(n: usize) -> Self {
            Int::from_bytes_be(Sign::Plus, &n.to_be_bytes()).into()
        }
    }
    impl From<(usize, usize)> for Cst {
        fn from((num, den): (usize, usize)) -> Self {
            let (num, den): (Int, Int) = (num.into(), den.into());
            Rat::new(num, den).into()
        }
    }
    impl From<Rat> for Cst {
        fn from(r: Rat) -> Self {
            Self::R(r)
        }
    }

    impl fmt::Display for Var {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            write!(fmt, "{}", self.id)
        }
    }

    impl Deref for SVar {
        type Target = Var;
        fn deref(&self) -> &Var {
            &self.var
        }
    }
    impl fmt::Display for SVar {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            write!(fmt, "{}@{}", self.id, if self.nxt { 1 } else { 0 })
        }
    }

    impl<V: fmt::Display> fmt::Display for PExpr<V> {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Self::Cst(cst) => cst.fmt(fmt),
                Self::Var(var) => var.fmt(fmt),
                Self::App { op, args } => {
                    write!(fmt, "({}", op)?;
                    for arg in args {
                        write!(fmt, " {}", arg)?
                    }
                    write!(fmt, ")")
                }
            }
        }
    }
    impl<C, V> From<C> for PExpr<V>
    where
        C: Into<Cst>,
    {
        fn from(cst: C) -> Self {
            Self::Cst(cst.into())
        }
    }
    impl<V> From<(Op, Vec<PExpr<V>>)> for PExpr<V> {
        fn from((op, args): (Op, Vec<PExpr<V>>)) -> Self {
            Self::App { op, args }
        }
    }
}
