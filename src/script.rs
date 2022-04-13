//! HSmt 2 scripts.

prelude!();

use expr::{Expr, MExpr};
use parse::ast::hsmt::*;

pub mod build;
pub mod frame;

// use frame::Frame;

/// A query result.
#[derive(Debug, Clone)]
pub enum QueryRes {
    /// True result.
    True,
    /// False result.
    False,
    /// Timeout, no result.
    Timeout(time::Duration),
    /// Unknown result.
    Unknown,
    /// No result.
    None,
}
impl QueryRes {
    /// Turns itself into a boolean, if possible.
    pub fn to_bool(&self) -> Option<bool> {
        match self {
            Self::True => Some(true),
            Self::False => Some(false),
            Self::Timeout(_) | Self::Unknown | Self::None => None,
        }
    }
}

/// A script is a sequence of [`Command`]s and a *meta-environment*.
///
/// The *meta-environment* stores *meta-variables* and the values they have. A *meta-variable*
/// is a script-level (not SMT-level) variable that stores the result of a [`Query`]. Currently,
/// this amounts to the boolean result of a check sat.
pub struct Script<'s> {
    /// Solver.
    pub solver: &'s mut Solver,
    /// Original commands, the full script.
    pub script: &'s Block<Expr, MExpr>,
    /// Stack of command frames (derivatives).
    pub stack: Vec<frame::Command<'s, Expr, MExpr>>,
    /// Meta-environment.
    pub meta_env: Map<String, QueryRes>,
    /// Current result, indicates we're going up.
    pub res: Option<QueryRes>,
}
impl<'s> Script<'s> {
    /// Constructor.
    pub fn new(solver: &'s mut Solver, script: &'s Block<Expr, MExpr>) -> Self {
        let mut stack = Vec::with_capacity(17);
        let block_frame = frame::Block::new(script).into();
        stack.push(block_frame);
        Self {
            solver,
            script,
            stack,
            meta_env: Map::new(),
            res: None,
        }
    }

    /// Performs an interpretation step.
    pub fn step(&mut self) {}
}
