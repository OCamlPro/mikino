//! AST.

crate::prelude!();

use expr::*;

/// Parse error.
#[derive(Debug)]
pub struct PError {
    /// Span where the error happened.
    pub span: Span,
    /// Actual error.
    pub error: Error,
}
impl fmt::Display for PError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            fmt,
            "[{}, {}] {}",
            self.span.start, self.span.end, self.error,
        )
    }
}
impl PError {
    /// Constructor.
    pub fn new(error: impl Into<Error>, span: impl Into<Span>) -> Self {
        let error = error.into();
        let span = span.into();
        PError { span, error }
    }

    /// Chains an error.
    pub fn chain_err<E>(mut self, err: impl FnOnce() -> E) -> Self
    where
        ErrorKind: From<E>,
    {
        self.error = self.error.chain_err(err);
        self
    }
}

/// Parse result.
pub type PRes<T> = Result<T, PError>;

/// A span in the input text.
#[derive(Debug, Clone, Copy)]
pub struct Span {
    /// Span's start (inclusive).
    pub start: usize,
    /// Span's end (exclusive).
    pub end: usize,
}
impl Span {
    /// Merges two spans, `self`'s start and `other`'s end.
    ///
    /// - illegal if `self.start > other.end`.
    pub fn merge(self, other: Self) -> Self {
        debug_assert!(self.start <= other.end);
        Span {
            start: self.start,
            end: other.end,
        }
    }
}
impl From<(usize, usize)> for Span {
    fn from((start, end): (usize, usize)) -> Self {
        Self { start, end }
    }
}

/// Wraps something with a span.
#[derive(Debug, Clone, Copy)]
pub struct Spn<T> {
    /// Value wrapped.
    pub inner: T,
    /// Span.
    pub span: Span,
}
impl<T> Spn<T> {
    /// Constructor.
    pub fn new(inner: T, span: impl Into<Span>) -> Self {
        let span = span.into();
        Self { inner, span }
    }

    /// Applies an operation to the inner value.
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> Spn<U> {
        Spn {
            inner: f(self.inner),
            span: self.span,
        }
    }

    /// Applies an operation yielding a result to the inner value.
    pub fn res_map<U>(
        self,
        mut f: impl FnMut(T) -> Result<U, &'static str>,
    ) -> Result<Spn<U>, &'static str> {
        let inner = f(self.inner)?;
        Ok(Spn::new(inner, self.span))
    }

    /// Unwraps `self`'s and `other`'s inner values and merges their spans.
    pub fn unwrap_merge<U>(self, other: Spn<U>) -> (T, U, Span) {
        (self.inner, other.inner, self.span.merge(other.span))
    }
}
impl<T> Deref for Spn<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.inner
    }
}

/// AST for the term structure.
pub enum Ast<'txt> {
    /// Spanned constant.
    Cst(Spn<Cst>),
    /// Variable, with a *pre* or *next* optional modifier.
    Var {
        /// Spanned identifier.
        ident: Spn<&'txt str>,
        /// Optional *pre* or *next* modifier.
        pon: Option<Span>,
    },
    /// Operator application.
    App {
        /// Spanned operator.
        op: Spn<Op>,
        /// Arguments.
        args: Vec<Ast<'txt>>,
        /// True if the operator application is closed, not used ATM.
        closed: bool,
    },
}

impl<'txt> Ast<'txt> {
    /// Constant constructor.
    pub fn cst(cst: Spn<Cst>) -> Self {
        Self::Cst(cst)
    }
    /// Variable constructor.
    pub fn var(ident: Spn<&'txt str>) -> Self {
        Self::Var { ident, pon: None }
    }
    /// State variable constructor.
    pub fn svar(ident: Spn<&'txt str>, pon: Option<Span>) -> Self {
        Self::Var { ident, pon }
    }

    /// Binary operator application.
    pub fn binapp(op: Spn<Op>, lft: Self, rgt: Self) -> Self {
        Self::App {
            op,
            args: vec![lft, rgt],
            closed: false,
        }
    }

    /// Unary operator application.
    pub fn unapp(op: Spn<Op>, arg: Self) -> Self {
        Self::App {
            op,
            args: vec![arg],
            closed: true,
        }
    }

    /// N-ary operator application.
    pub fn app(op: Spn<Op>, args: Vec<Self>) -> Self {
        Self::App {
            op,
            args,
            closed: true,
        }
    }

    /// Closes the application.
    pub fn close(&mut self) {
        match self {
            Self::App { closed, .. } => *closed = true,
            Self::Var { .. } | Self::Cst(_) => (),
        }
    }

    /// Turns itself into an expression from some declarations.
    pub fn to_sexpr(self, decls: &trans::Decls) -> PRes<SExpr> {
        self.inner_to_expr(|var, next_opt| {
            let svar = if next_opt.is_some() {
                decls.get_next_var(var.inner)
            } else {
                decls.get_curr_var(var.inner)
            }
            .ok_or_else(|| PError::new(format!("unknown variable `{}`", var.inner), var.span))?;
            Ok(Spn::new(
                SExpr::new_var(svar),
                var.span.merge(next_opt.unwrap_or(var.span)),
            ))
        })
    }

    /// Turns itself into a stateless expression from some declarations.
    pub fn to_expr(self, decls: &trans::Decls) -> PRes<Expr> {
        self.inner_to_expr(|var, next_opt| {
            if let Some(span) = next_opt {
                return Err(PError::new("illegal *next* modifier", span));
            }
            let svar = decls.get_var(var.inner).ok_or_else(|| {
                PError::new(format!("unknown variable `{}`", var.inner), var.span)
            })?;
            Ok(Spn::new(
                Expr::new_var(svar),
                var.span.merge(next_opt.unwrap_or(var.span)),
            ))
        })
    }

    /// Turns itself into an expression.
    ///
    /// - `handle_var` turns variables into actual expression variables.
    pub fn inner_to_expr<V: HasTyp>(
        self,
        mut handle_var: impl FnMut(Spn<&'txt str>, Option<Span>) -> PRes<Spn<PExpr<V>>>,
    ) -> PRes<PExpr<V>> {
        let mut stack: Vec<(Spn<Op>, Vec<PExpr<V>>, _, bool)> = Vec::with_capacity(17);
        let mut current = self;

        'go_down: loop {
            let mut res: Spn<PExpr<V>> = match current {
                Ast::Cst(cst) => cst.map(PExpr::new_cst),
                Ast::Var { ident, pon } => handle_var(ident, pon)?,
                Ast::App { op, args, closed } => {
                    let mut args = args.into_iter();
                    if let Some(next) = args.next() {
                        current = next;
                    } else {
                        return Err(PError::new("illegal unary operator application", op.span));
                    }
                    stack.push((op, Vec::with_capacity(args.len()), args, closed));
                    continue 'go_down;
                }
            };

            'go_up: while let Some((op, mut args, mut todo, closed)) = stack.pop() {
                if let Some(next) = todo.next() {
                    args.push(res.inner);
                    current = next;
                    stack.push((op, args, todo, closed));
                    continue 'go_down;
                } else {
                    if let Some((up_op, up_args, _, _)) = stack.last_mut() {
                        if up_op.inner == op.inner && op.inner.is_left_associative() {
                            up_op.span = op.span;
                            up_args.extend(args);
                            continue 'go_up;
                        }
                    }
                    args.push(res.inner);
                    let expr =
                        PExpr::new_op(op.inner, args).map_err(|e| PError::new(e, op.span))?;
                    res = Spn::new(expr, op.span);
                    continue 'go_up;
                }
            }

            return Ok(res.inner);
        }
    }
}

impl<'txt> fmt::Display for Ast<'txt> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cst(cst) => cst.fmt(fmt),
            Self::Var { ident, pon } => {
                ident.fmt(fmt)?;
                if pon.is_some() {
                    "'".fmt(fmt)?
                }
                Ok(())
            }
            &Self::App {
                op,
                ref args,
                closed,
            } => {
                let closed = closed || true;
                if closed {
                    "(".fmt(fmt)?
                }

                let hsmt = op.hsmt_str();

                if args.len() == 1 {
                    hsmt[0].fmt(fmt)?;
                    args[0].fmt(fmt)?
                } else {
                    for (idx, arg) in args.iter().enumerate() {
                        if idx > 0 || hsmt.len() > 1 {
                            let pref = if idx > 0 { " " } else { "" };
                            let hsmt_idx = std::cmp::min(hsmt.len() - 1, idx);
                            write!(fmt, "{}{} ", pref, hsmt[hsmt_idx])?;
                        }
                        arg.fmt(fmt)?
                    }
                }

                if closed {
                    ")".fmt(fmt)?
                }
                Ok(())
            }
        }
    }
}