//! Transition system structures and helpers.
//!
//! A transition system is composed of
//!
//! - an *initial* predicate,
//! - a *transition* predicate, and
//! - a list of named Proof Obligations (POs).
//!
//! The initial predicate and the POs are stateless expressions [`expr::Expr`]. The transition
//! relation is a stateful expression [`expr::SExpr`].
//!
//! A system also contains declarations [`Decls`] for its state variables
//!
//! [`expr::Expr`]: ../expr/type.Expr.html (The Expr type)
//! [`expr::SExpr`]: ../expr/type.SExpr.html (The SExpr type)
//! [`Decls`]: struct.Decls.html (The Decls struct)

crate::prelude!();

use expr::{Expr, SExpr, SVar, Typ, Var};

/// Variable declarations for transition systems.
#[derive(Debug)]
pub struct Decls {
    /// Map from variable identifiers to types.
    id_to_typs: Map<String, Typ>,
}
impl fmt::Display for Decls {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        // Get the IDs ordered.
        let mut ids: Vec<_> = self.id_to_typs.iter().collect();
        ids.sort_by(|(id_lft, _), (id_rgt, _)| id_lft.cmp(id_rgt));

        let (clusters, last): (_, Option<(Typ, Vec<&String>)>) =
            ids.into_iter()
                .fold((vec![], None), |(mut list, last_opt), (id, typ)| {
                    if let Some((last_typ, mut last_vars)) = last_opt {
                        if *typ == last_typ {
                            last_vars.push(id);
                            return (list, Some((last_typ, last_vars)));
                        } else {
                            list.push((last_typ, last_vars));
                        }
                    }
                    (list, Some((*typ, vec![id])))
                });

        for (idx, (typ, vars)) in clusters.into_iter().chain(last).enumerate() {
            if idx > 0 {
                write!(fmt, "\n")?;
            }
            for (idx, var) in vars.into_iter().enumerate() {
                if idx > 0 {
                    write!(fmt, " ")?;
                }
                var.fmt(fmt)?;
            }
            write!(fmt, ": {},", typ)?;
        }

        Ok(())
    }
}
impl Decls {
    /// Constructor.
    pub fn new() -> Self {
        Self {
            id_to_typs: Map::new(),
        }
    }

    /// Length of the longest identifier (used for formatting).
    pub fn max_id_len(&self) -> usize {
        self.id_to_typs
            .iter()
            .fold(0, |max, (id, _)| usize::max(max, id.len()))
    }

    /// Declaration pretty-printer.
    pub fn to_ml_string(&self) -> String {
        let mut typ_to_ids = Map::new();
        for (id, typ) in &self.id_to_typs {
            let is_new = typ_to_ids.entry(*typ).or_insert_with(Set::new).insert(id);
            assert!(is_new)
        }

        let mut s = String::new();
        for (idx, (typ, ids)) in typ_to_ids.into_iter().enumerate() {
            if idx > 0 {
                s.push_str("\n")
            }
            for (idx, id) in ids.iter().enumerate() {
                if idx > 0 {
                    s.push_str(", ")
                }
                s.push_str(id)
            }
            s.push_str(": ");
            s.push_str(&typ.to_string())
        }
        s
    }

    /// Builds a variable corresponding to an identifier.
    ///
    /// None if the identifier of the variable is unknown.
    pub fn get_var<Str: AsRef<str>>(&self, id: Str) -> Option<Var> {
        let id = id.as_ref();
        self.id_to_typs
            .get(id)
            .map(|typ_ref| Var::new(id, *typ_ref))
    }

    /// Builds a current state variable corresponding to an identifier.
    ///
    /// None if the identifier of the variable is unknown.
    pub fn get_curr_var<Str: AsRef<str>>(&self, id: Str) -> Option<SVar> {
        self.get_var(id).map(|var| SVar::new_curr(var))
    }

    /// Builds a next state variable corresponding to an identifier.
    ///
    /// None if the identifier of the variable is unknown.
    pub fn get_next_var<Str: AsRef<str>>(&self, id: Str) -> Option<SVar> {
        self.get_var(id).map(|var| SVar::new_next(var))
    }

    /// Registers a variable.
    ///
    /// Returns the previous type if `id` was already registered, and `None` otherwise.
    pub fn register<S: Into<String>>(&mut self, id: S, typ: Typ) -> Option<Typ> {
        self.id_to_typs.insert(id.into(), typ)
    }

    /// An iterator over all the variables declared as [`Var`]s.
    ///
    /// [`Var`]: ../expr/struct.Var.html (The Var struct)
    pub fn all<'a>(&'a self) -> impl Iterator<Item = Var> + 'a {
        self.id_to_typs.iter().map(|(id, typ)| Var::new(id, *typ))
    }
}

/// A transition system with an initial state and transition relation.
pub struct Sys {
    /// Variable declarations.
    decls: Decls,
    /// Initial predicate, a stateless expression.
    init: Expr,
    /// Transition predicate, a stateful expression.
    trans: SExpr,
    /// Proof obligations for this system.
    po_s: Map<String, Expr>,
}
impl Sys {
    /// Constructor.
    pub fn new(decls: Decls, init: Expr, trans: SExpr, po_s: Map<String, Expr>) -> Self {
        Self {
            decls,
            init,
            trans,
            po_s,
        }
    }

    /// Pretty, multi-line string representation of the system.
    pub fn to_ml_string(&self) -> String {
        let mut s = String::new();
        s.push_str("decls {\n");
        for line in self.decls.to_ml_string().lines() {
            s.push_str("    ");
            s.push_str(line);
            s.push_str("\n")
        }
        s.push_str("}");
        s.push_str("\ninit:\n    ");
        s.push_str(&self.init.to_string());
        s.push_str("\ntrans:\n    ");
        s.push_str(&self.trans.to_string());
        s.push_str("\npo_s:");
        for (name, po) in &self.po_s {
            s.push_str("\n    \"");
            s.push_str(name);
            s.push_str("\": ");
            s.push_str(&po.to_string())
        }
        s
    }

    /// Variable declaration accessor.
    pub fn decls(&self) -> &Decls {
        &self.decls
    }
    /// Initial predicate accessor.
    pub fn init(&self) -> &Expr {
        &self.init
    }
    /// Transition predicate accessor.
    pub fn trans(&self) -> &SExpr {
        &self.trans
    }
    /// Proof obligation accessor.
    pub fn po_s(&self) -> &Map<String, Expr> {
        &self.po_s
    }
}

/// Builds an expression.
///
/// - identifiers must be written as `(var_name: var_typ)`, without any quotes.
#[macro_export]
macro_rules! build_trans_expr {
    ($state:tt, $decls:expr, true) => ( expr::PExpr::from(true) );
    ($state:tt, $decls:expr, false) => ( expr::PExpr::from(false) );

    (stateless, $decls:expr, $var:ident) => (
        if let Some(var) = $decls.get_var(stringify!($var)) {
            expr::PExpr::new_var(var)
        } else {
            panic!("undeclared variable `{}`", stringify!($var))
        }
    );
    (stateful, $decls:expr, ($var:ident @ 0)) => (
        if let Some(var) = $decls.get_curr_var(stringify!($var)) {
            expr::PExpr::new_var(var)
        } else {
            panic!("undeclared variable `{}`", stringify!($var))
        }
    );
    (stateful, $decls:expr, ($var:ident @ 1)) => (
        if let Some(var) = $decls.get_next_var(stringify!($var)) {
            expr::PExpr::new_var(var)
        } else {
            panic!("undeclared variable `{}`", stringify!($var))
        }
    );

    ($state:tt, $decls:expr, ($op:tt $($args:tt)*) ) => (
        expr::PExpr::from((
            $crate::build_trans_expr!(@op $op),
            vec![ $($crate::build_trans_expr!($state, $decls, $args)),* ],
        ))
    );

    ($state:tt, $decls:expr, $cst:expr) => ( expr::PExpr::from($cst) );

    (@op ite) => ( expr::Op::Ite );
    (@op +) => ( expr::Op::Add );
    (@op -) => ( expr::Op::Sub );
    (@op *) => ( expr::Op::Mul );
    (@op /) => ( expr::Op::Div );
    (@op %) => ( expr::Op::Mod );
    (@op >=) => ( expr::Op::Ge );
    (@op <=) => ( expr::Op::Le );
    (@op >) => ( expr::Op::Gt );
    (@op <) => ( expr::Op::Lt );
    (@op =) => ( expr::Op::Eq );
    (@op not) => ( expr::Op::Not );
    (@op and) => ( expr::Op::And );
    (@op or) => ( expr::Op::Or );
}
