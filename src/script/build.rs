//! Builds a script from a script AST.

prelude!(
    parse::ast::{hsmt::*, Ast, PRes, PError, Spn, Span},
    expr::{Expr, MExpr, MetaVar},
    trans::Decls,
);

/// Meta-declarations: scoped, unlike normal declarations.
pub type MDecls = Decls;

/// Stack frames for [`doit`](doit()).
pub enum Frame<'input> {
    /// Meta-let info.
    MLet(MDecls, Spn<String>),
    /// Block info.
    Block(
        MDecls,
        Vec<Command<Expr, MExpr>>,
        std::vec::IntoIter<Command<Ast<'input>, Ast<'input>>>,
    ),
    /// Ite info, when in the condition.
    IteCnd(
        MDecls,
        Decls,
        Span,
        Block<Ast<'input>, Ast<'input>>,
        Block<Ast<'input>, Ast<'input>>,
        Option<Block<Ast<'input>, Ast<'input>>>,
    ),
    /// Ite info, when in the then branch.
    IteThn(
        MDecls,
        Decls,
        Span,
        Either<Spn<MetaVar>, CheckSat>,
        Block<Ast<'input>, Ast<'input>>,
        Option<Block<Ast<'input>, Ast<'input>>>,
    ),
    /// Ite info, when in the else branch.
    IteEls(
        MDecls,
        Decls,
        Span,
        Either<Spn<MetaVar>, CheckSat>,
        (Block<Expr, MExpr>, Decls),
        Option<Block<Ast<'input>, Ast<'input>>>,
    ),
    /// Ite info, when in the otherwise branch.
    IteOtw(
        MDecls,
        Decls,
        Span,
        Either<Spn<MetaVar>, CheckSat>,
        (Block<Expr, MExpr>, Decls),
        (Block<Expr, MExpr>, Decls),
    ),
}

/// Turns this on to show DEBUG information.
///
/// Probably should do this using the `log` crate.
const DEBUG: bool = false;

/// Turns a script AST into an actual script.
pub fn doit(block: Block<Ast, Ast>) -> PRes<Command<Expr, MExpr>> {
    let mut stack: Vec<Frame> = Vec::with_capacity(11);
    let mut curr: Command<Ast, Ast> = block.into();
    let mut decls = Decls::new();
    let mut meta_decls = MDecls::new();

    macro_rules! show_meta {
        ($blah:tt $cmd:expr) => {
            if DEBUG {
                let pref = str::repeat("  ", stack.len());
                println!(
                    "{}[{}] {}: {}, panics: {}",
                    pref,
                    stringify!($blah),
                    stringify!($cmd),
                    $cmd.desc(),
                    $cmd.panics(),
                );
                if meta_decls.all().count() > 0 {
                    println!("{}- meta declarations:", pref);
                    for var in meta_decls.all() {
                        println!("{}  {}: {}", pref, var, var.typ());
                    }
                }
                if decls.all().count() > 0 {
                    println!("{}- declarations:", pref);
                    for var in decls.all() {
                        println!("{}  {}: {}", pref, var, var.typ());
                    }
                }
            }
        };
    }

    'go_down: loop {
        show_meta!(down curr);
        let mut res: Command<Expr, MExpr> = match curr {
            Command::SetOptions(opts) => opts.into(),
            Command::Echo(e) => e.into(),
            Command::Query(Query::Panic(p)) => p.into(),
            Command::GetModel(gm) => gm.into(),
            Command::Vars(v) => {
                let clashes = decls.merge(&v.decls);
                if let Some(clashes) = clashes {
                    debug_assert!(!clashes.is_empty());
                    let clash_count = clashes.len();
                    let plural = if clash_count > 1 { "s" } else { "" };
                    let mut msg = format!("re-declaring {} variable{}:", clash_count, plural);
                    for (idx, (id, _)) in clashes.into_iter().enumerate() {
                        msg.push_str(if idx > 0 { ", " } else { " " });
                        msg.push_str(&id);
                    }
                    return Err(PError::new(msg, v.span));
                }
                Command::Vars(v)
            }
            Command::MLet(ml) => {
                stack.push(Frame::MLet(meta_decls.clone(), ml.lhs));
                curr = ml.rhs.into();
                continue 'go_down;
            }
            Command::Assert(a) => {
                let expr = a.expr.to_expr(&decls)?;
                Assert::new(a.span, expr).into()
            }

            Command::Query(Query::Block(b)) => {
                let count = b.content.len();
                let mut todo = b.content.into_iter();
                if let Some(first) = todo.next() {
                    let res = Vec::with_capacity(count);
                    curr = first;
                    stack.push(Frame::Block(meta_decls.clone(), res, todo));
                    continue 'go_down;
                } else {
                    Block::new(vec![]).into()
                }
            }
            Command::Query(Query::CheckSat(c)) => {
                // Check for unknown literals.
                let mut unknown = None;
                for lit in c.assuming.iter() {
                    if !decls.contains(&lit.inner) {
                        let unknown = unknown.get_or_insert_with(Vec::new);
                        unknown.push(&lit.inner)
                    }
                }
                if let Some(unknown) = unknown {
                    let plural = if unknown.len() > 1 { "s" } else { "" };
                    let mut err = format!(
                        "check sat mentions {} unknown literal{}:",
                        unknown.len(),
                        plural,
                    );
                    for (idx, lit) in unknown.into_iter().enumerate() {
                        if idx > 0 {
                            err.push(',');
                        }
                        err.push(' ');
                        err.push_str(lit);
                    }
                    return Err(PError::new(err, c.span));
                }

                c.into()
            }
            Command::Query(Query::Ite(ite)) => match ite.cnd {
                Either::Left(mvar) => {
                    if !meta_decls.contains(&mvar.inner.ident) {
                        return Err(PError::new(
                            format!("unknown meta-variable `{}`", mvar.inner.ident),
                            mvar.span,
                        ));
                    }

                    curr = ite.thn.into();
                    stack.push(Frame::IteThn(
                        meta_decls.clone(),
                        decls.clone(),
                        ite.span,
                        Either::Left(mvar),
                        ite.els,
                        ite.otw,
                    ));
                    continue 'go_down;
                }
                Either::Right(check_sat) => {
                    curr = check_sat.into();
                    stack.push(Frame::IteCnd(
                        meta_decls.clone(),
                        decls.clone(),
                        ite.span,
                        ite.thn,
                        ite.els,
                        ite.otw,
                    ));
                    continue 'go_down;
                }
            },
        };

        'go_up: loop {
            show_meta!(up res);
            match stack.pop() {
                Some(Frame::MLet(mdecls, id)) => match res {
                    Command::Query(Query::CheckSat(c)) => {
                        meta_decls = mdecls;
                        // Shadowing is fine.
                        let _prev = meta_decls.register(id.inner.clone(), Typ::Bool);
                        res = MLet::new(id, c).into();
                        continue 'go_up;
                    }
                    _ => panic!("[fatal] expected check sat, got {:#?}", res),
                },
                Some(Frame::Block(mdecls, mut res_vec, mut todo)) => {
                    res_vec.push(res);
                    if let Some(next) = todo.next() {
                        curr = next;
                        stack.push(Frame::Block(mdecls, res_vec, todo));
                        continue 'go_down;
                    } else {
                        res = Block::new(res_vec).into();
                        meta_decls = mdecls;
                        continue 'go_up;
                    }
                }
                Some(Frame::IteCnd(mdecls, vdecls, span, thn, els, otw)) => match res {
                    Command::Query(Query::CheckSat(c)) => {
                        curr = thn.into();
                        stack.push(Frame::IteThn(
                            mdecls,
                            vdecls,
                            span,
                            Either::Right(c),
                            els,
                            otw,
                        ));
                        continue 'go_down;
                    }
                    res => panic!("[fatal] expected check sat, got {:#?}", res),
                },
                Some(Frame::IteThn(mdecls, vdecls, span, cnd, els, otw)) => match res {
                    Command::Query(Query::Block(thn)) => {
                        let thn_decls = mem::replace(&mut decls, vdecls.clone());
                        meta_decls = mdecls.clone();
                        curr = els.into();
                        stack.push(Frame::IteEls(
                            mdecls,
                            vdecls,
                            span,
                            cnd,
                            (thn, thn_decls),
                            otw,
                        ));
                        continue 'go_down;
                    }
                    res => panic!("[fatal] expected block, got {:#?}", res),
                },
                Some(Frame::IteEls(mdecls, vdecls, span, cnd, thn, otw)) => match res {
                    Command::Query(Query::Block(els)) => {
                        meta_decls = mdecls.clone();
                        if let Some(otw) = otw {
                            let els_decls = mem::replace(&mut decls, vdecls.clone());
                            curr = otw.into();
                            stack.push(Frame::IteOtw(
                                mdecls,
                                vdecls,
                                span,
                                cnd,
                                thn,
                                (els, els_decls),
                            ));
                            continue 'go_down;
                        } else {
                            let (thn, thn_decls) = thn;

                            match (thn.panics(), els.panics()) {
                                (true, true) => {
                                    let _ = decls.merge(&thn_decls);
                                }
                                (true, false) => {
                                    decls = thn_decls;
                                }
                                (false, true) => {
                                    decls = thn_decls;
                                }
                                (false, false) => {
                                    let _ = decls.inter(&thn_decls);
                                }
                            }
                            res = Ite::new(span, cnd, thn, els, None).into();
                            continue 'go_up;
                        }
                    }
                    res => panic!("[fatal] expected block, got {:#?}", res),
                },
                Some(Frame::IteOtw(
                    mdecls,
                    _vdecls,
                    span,
                    cnd,
                    (thn, thn_decls),
                    (els, els_decls),
                )) => match res {
                    Command::Query(Query::Block(otw)) => {
                        meta_decls = mdecls;
                        match (thn.panics(), els.panics(), otw.panics()) {
                            // All branches panic.
                            (true, true, true) => {
                                let _ = decls.merge(&thn_decls);
                                let _ = decls.merge(&els_decls);
                            }

                            // Only one branch does not panic.
                            (true, true, false) => (),
                            (false, true, true) => {
                                decls = thn_decls;
                            }
                            (true, false, true) => {
                                decls = els_decls;
                            }

                            // Two branches do not panic.
                            (false, false, true) => {
                                decls = thn_decls;
                                let _ = decls.inter(&els_decls);
                            }
                            (false, true, false) => {
                                let _ = decls.inter(&thn_decls);
                            }
                            (true, false, false) => {
                                let _ = decls.inter(&els_decls);
                            }

                            // No branch panics.
                            (false, false, false) => {
                                let _ = decls.inter(&thn_decls);
                                let _ = decls.inter(&els_decls);
                            }
                        }

                        res = Ite::new(span, cnd, thn, els, Some(otw)).into();
                        continue 'go_up;
                    }
                    _ => panic!("[fatal] expected block, got {:#?}", res),
                },
                None => match res {
                    Command::Query(Query::Block(b)) => {
                        return Ok(b.into());
                    }
                    _ => panic!(
                        "[fatal] script parsing cannot produce non-block command but yielded {:#?}",
                        res,
                    ),
                },
            }
        }
    }
}
