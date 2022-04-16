//! AST.

crate::prelude!();

use expr::*;

pub mod hsmt;

/// Parse error.
#[derive(Debug)]
pub struct PError {
    /// Span where the error happened.
    pub span: Span,
    /// Actual error.
    pub error: ErrorChain,
}
impl fmt::Display for PError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            fmt,
            "[{}, {}] {}",
            self.span.start, self.span.end, self.error.source,
        )
    }
}
impl PError {
    /// Constructor.
    pub fn new(error: impl Into<ErrorChain>, span: impl Into<Span>) -> Self {
        let error = error.into();
        let span = span.into();
        PError { span, error }
    }

    /// Chains an error.
    pub fn chain_err<E>(mut self, err: impl FnOnce() -> E) -> Self
    where
        Error: From<E>,
    {
        self.error = self.error.chain_err(err);
        self
    }

    /// Turns itself in a nice error.
    pub fn into_error(self, txt: &str) -> ErrorChain {
        let span = self.span;
        let (prev, row, col, line, next) = span.pretty_of(txt);
        let err = Error::parse("", row, col, line, prev, next);
        err.extend(self.error.into_iter())
    }

    /// Turns itself in a nice error.
    pub fn new_error(span: Span, txt: &str, msg: impl Into<String>) -> Error {
        let (prev, row, col, line, next) = span.pretty_of(txt);
        Error::parse(msg, row, col, line, prev, next)
    }
}

/// Parse result.
pub type PRes<T> = Result<T, PError>;

/// A span in the input text.
#[readonly::make]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// Span's start (inclusive).
    pub start: usize,
    /// Span's end (exclusive).
    pub end: usize,
}
impl Span {
    /// Constructor.
    pub fn new(start: usize, end: usize) -> Self {
        debug_assert!(start <= end);
        Span { start, end }
    }
    /// Merges two spans, `self`'s start and `other`'s end.
    ///
    /// - illegal if `self.start > other.end`.
    pub fn merge(self, other: Self) -> Self {
        (self.start, other.end).into()
    }

    /// Extracts the relevant line of the input, and the previous/next line if any.
    pub fn pretty_of(self, text: &str) -> (Option<String>, usize, usize, String, Option<String>) {
        if text.is_empty() {
            assert_eq!(self.start, 0);
            assert_eq!(self.end, 0);
            return (None, 0, 0, "<EOI>".into(), None);
        }
        let mut lines = text.lines().enumerate();

        let mut count = self.start;
        let mut prev_line = None;

        while let Some((row, line)) = lines.next() {
            if line.len() >= count {
                let (line, next) = {
                    let next = lines.next().map(|(_, s)| s.to_string());
                    if next.is_none() {
                        (format!("{}{}", line, "<EOI>"), next)
                    } else {
                        (line.into(), next)
                    }
                };
                return (prev_line.map(String::from), row, count, line, next);
            }

            count -= line.len() + 1;
            prev_line = Some(line);
        }

        panic!(
            "illegal offset {} on text of length {}",
            self.start,
            text.len()
        );
    }

    /// Pretty multi-line string representation.
    pub fn pretty_ml_of(
        self,
        text: impl AsRef<str>,
        style: impl Style,
        msg: impl AsRef<str>,
    ) -> String {
        let text = text.as_ref();
        let msg = msg.as_ref();
        let (prev, row, col, line, next) = self.pretty_of(text);
        let (row_str, col_str) = ((row + 1).to_string(), (col + 1).to_string());
        let offset = {
            let mut offset = 0;
            let mut cnt = 0;
            for c in line.chars() {
                if cnt < col {
                    offset += 1;
                    cnt += c.len_utf8();
                } else {
                    break;
                }
            }
            offset
        };
        let mut s = format!(
            "at {}:{}\n{} |{}\n{} | {}",
            style.bold(&row_str),
            style.bold(&col_str),
            " ".repeat(row_str.len()),
            prev.as_ref()
                .map(|s| format!(" {}", s))
                .unwrap_or("".into()),
            style.bold(&row_str),
            line,
        );
        s.push_str(&format!(
            "\n{} | {}{} {}",
            " ".repeat(row_str.len()),
            " ".repeat(offset),
            style.red("^~~~"),
            style.red(if msg.is_empty() { "here" } else { msg }),
        ));
        if let Some(next) = next {
            s.push_str(&format!("\n{} | {}", " ".repeat(row_str.len()), next))
        }
        s
    }
}
impl From<(usize, usize)> for Span {
    fn from((start, end): (usize, usize)) -> Self {
        Self::new(start, end)
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
impl<T: PartialEq> PartialEq for Spn<T> {
    fn eq(&self, that: &Self) -> bool {
        self.inner == that.inner
    }
}
impl<T: Eq> Eq for Spn<T> {}
impl<T> Spn<T> {
    /// Constructor.
    pub fn new(inner: T, span: impl Into<Span>) -> Self {
        let span = span.into();
        Self { inner, span }
    }

    /// Applies an operation to the inner value.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spn<U> {
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
impl From<Spn<&str>> for Spn<String> {
    fn from(spn: Spn<&str>) -> Self {
        spn.map(|s| s.into())
    }
}

/// AST for the term structure.
#[derive(Debug, Clone, PartialEq, Eq)]
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

    /// Span accessor.
    pub fn span(&self) -> Span {
        match self {
            Self::Var { ident, .. } => ident.span,
            Self::Cst(c) => c.span,
            Self::App { op, .. } => op.span,
        }
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

    /// True if `self` is an if-then-else application.
    pub fn is_ite(&self) -> bool {
        match self {
            Self::App { op, .. } if **op == Op::Ite => true,
            _ => false,
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
                if pon.is_some() {
                    "'".fmt(fmt)?
                }
                ident.fmt(fmt)?;
                Ok(())
            }
            &Self::App {
                op,
                ref args,
                closed: _,
            } if *op == Op::Ite => {
                assert_eq!(args.len(), 3);

                write!(fmt, "if {} {{ {} }} else ", args[0], args[1])?;

                if args[2].is_ite() {
                    args[2].fmt(fmt)
                } else {
                    write!(fmt, "{{ {} }}", args[2])
                }
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
