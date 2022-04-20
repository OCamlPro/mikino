//! AST structures for expressions and scripts.

crate::prelude!();

pub mod script;

/// AST for the term structure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr<'txt> {
    /// Spanned constant.
    Cst(Spn<expr::Cst>),
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
        op: Spn<expr::Op>,
        /// Arguments.
        args: Vec<Expr<'txt>>,
        /// True if the operator application is closed, not used ATM.
        closed: bool,
    },
}

impl<'txt> Expr<'txt> {
    /// Constant constructor.
    pub fn cst(cst: Spn<expr::Cst>) -> Self {
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
    pub fn binapp(op: Spn<expr::Op>, lft: Self, rgt: Self) -> Self {
        Self::App {
            op,
            args: vec![lft, rgt],
            closed: false,
        }
    }

    /// Unary operator application.
    pub fn unapp(op: Spn<expr::Op>, arg: Self) -> Self {
        Self::App {
            op,
            args: vec![arg],
            closed: true,
        }
    }

    /// N-ary operator application.
    pub fn app(op: Spn<expr::Op>, args: Vec<Self>) -> Self {
        Self::App {
            op,
            args,
            closed: true,
        }
    }

    /// True if `self` is an if-then-else application.
    pub fn is_ite(&self) -> bool {
        match self {
            Self::App { op, .. } if **op == expr::Op::Ite => true,
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
    pub fn to_sexpr(self, decls: &trans::Decls) -> PRes<expr::SExpr> {
        self.inner_to_expr(|var, next_opt| {
            let svar = if next_opt.is_some() {
                decls.get_next_var(var.inner)
            } else {
                decls.get_curr_var(var.inner)
            }
            .ok_or_else(|| PError::new(format!("unknown variable `{}`", var.inner), var.span))?;
            Ok(Spn::new(
                expr::SExpr::new_var(svar),
                var.span.merge(next_opt.unwrap_or(var.span)),
            ))
        })
    }

    /// Turns itself into a stateless expression from some declarations.
    pub fn to_expr(self, decls: &trans::Decls) -> PRes<expr::Expr> {
        self.inner_to_expr(|var, next_opt| {
            if let Some(span) = next_opt {
                return Err(PError::new("illegal *next* modifier", span));
            }
            let svar = decls.get_var(var.inner).ok_or_else(|| {
                PError::new(format!("unknown variable `{}`", var.inner), var.span)
            })?;
            Ok(Spn::new(
                expr::Expr::new_var(svar),
                var.span.merge(next_opt.unwrap_or(var.span)),
            ))
        })
    }

    /// Turns itself into an expression.
    ///
    /// - `handle_var` turns variables into actual expression variables.
    pub fn inner_to_expr<V: HasTyp>(
        self,
        mut handle_var: impl FnMut(Spn<&'txt str>, Option<Span>) -> PRes<Spn<expr::PExpr<V>>>,
    ) -> PRes<expr::PExpr<V>> {
        let mut stack: Vec<(Spn<expr::Op>, Vec<expr::PExpr<V>>, _, bool)> = Vec::with_capacity(17);
        let mut current = self;

        'go_down: loop {
            let mut res: Spn<expr::PExpr<V>> = match current {
                Expr::Cst(cst) => cst.map(expr::PExpr::new_cst),
                Expr::Var { ident, pon } => handle_var(ident, pon)?,
                Expr::App { op, args, closed } => {
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
                        expr::PExpr::new_op(op.inner, args).map_err(|e| PError::new(e, op.span))?;
                    res = Spn::new(expr, op.span);
                    continue 'go_up;
                }
            }

            return Ok(res.inner);
        }
    }
}

impl<'txt> fmt::Display for Expr<'txt> {
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
            } if *op == expr::Op::Ite => {
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
