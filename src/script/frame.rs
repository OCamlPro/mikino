//! Frame stuff.

crate::prelude!();

use super::{CurrentCmd, QueryRes};
use parse::ast::hsmt;

/// An action that happens when going up the frame stack.
pub enum UpRes<'script> {
    /// Sets a meta-variable.
    Set {
        /// Meta-variable to set.
        meta_var: &'script str,
        /// Meta-variable value.
        value: QueryRes,
    },
    /// No result, summary of what happened.
    Unit(String),
    /// Query result, must go up.
    QueryRes(QueryRes),
}

/// Frame trait.
pub trait Frame<'s, E, ME> {
    /// Produces the current command.
    fn current(&self) -> Res<CurrentCmd<'s, E, ME>>;
}

/// Derivative of a block.
#[derive(Debug, Clone)]
pub struct Block<'script, E, ME> {
    /// Original block.
    pub block: &'script hsmt::Block<E, ME>,
    /// Index of the current command in the block.
    pub current: usize,
}
impl<'script, E, ME> Frame<'script, E, ME> for Block<'script, E, ME> {
    fn current(&self) -> Res<CurrentCmd<'script, E, ME>> {
        let current = &self.block[self.current];
        Ok(current.into())
    }
}

impl<'script, E, ME> Block<'script, E, ME> {
    /// Constructor.
    pub fn new(block: &'script hsmt::Block<E, ME>) -> Self {
        Self { block, current: 0 }
    }
}

impl<'script, E, ME> Iterator for Block<'script, E, ME> {
    type Item = &'script hsmt::Command<E, ME>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.block.content.len() {
            let res = Some(&self.block.content[self.current]);
            self.current += 1;
            res
        } else {
            None
        }
    }
}

/// Derivative of an [`MLet`].
///
/// Stores no info besides the original `MLet`: if we are in an `MLet`, we are necessarily in its
/// block.
#[derive(Debug, Clone)]
pub struct MLet<'script> {
    /// Original [`MLet`].
    pub mlet: &'script hsmt::MLet,
}

impl<'script> MLet<'script> {
    /// Constructor.
    pub fn new(mlet: &'script hsmt::MLet) -> Self {
        Self { mlet }
    }
}

/// Specifies a position in an [`Ite`].
#[derive(Debug, Clone, Copy)]
pub enum ItePos {
    /// Currently in the check sat condition.
    Cnd,
    /// Currently in the `then` branch.
    Thn,
    /// Currently in the `else` branch.
    Els,
    /// Currently in the `otherwise` branch.
    Otw,
}

/// Derivative of an [`Ite`].
#[derive(Debug, Clone)]
pub struct Ite<'script, E, ME> {
    /// Original [`Ite`].
    pub ite: &'script hsmt::Ite<E, ME>,
    /// Current position in the [`Ite`].
    pub pos: ItePos,
}
impl<'script, E, ME> Frame<'script, E, ME> for Ite<'script, E, ME> {
    fn current(&self) -> Res<CurrentCmd<'script, E, ME>> {
        match self.pos {
            ItePos::Cnd => Ok(self
                .ite
                .cnd
                .as_ref()
                .right()
                .ok_or(
                    "trying to access query condition of if-then-else, \
                but condition is an expression",
                )?
                .into()),
            ItePos::Thn => {
                let curr = &self.ite.thn;
                Ok(curr.into())
            }
            ItePos::Els => {
                let curr = &self.ite.els;
                Ok(curr.into())
            }
            ItePos::Otw => Ok(self
                .ite
                .otw
                .as_ref()
                .ok_or("trying to access otherwise branch of if-then-else, but there is no otherwise branch")?
                .into()),
        }
    }
}

impl<'script, E, ME> Ite<'script, E, ME> {
    /// Constructor.
    ///
    /// Fails if the condition of the [`Ite`] is not a check sat.
    pub fn new(ite: &'script hsmt::Ite<E, ME>, pos: ItePos) -> Res<Self> {
        match pos {
            ItePos::Cnd => {
                if ite.cnd.is_left() {
                    bail!("cannot explore the condition of an if-then-else with a non-check-sat condition")
                }
            }
            ItePos::Thn | ItePos::Els | ItePos::Otw => (),
        }
        Ok(Self { ite, pos })
    }
    /// Constructor for an exploration of the condition.
    pub fn new_cnd(ite: &'script hsmt::Ite<E, ME>) -> Res<Self> {
        Self::new(ite, ItePos::Cnd)
    }
    /// Constructor for an exploration of the then branch.
    pub fn new_thn(ite: &'script hsmt::Ite<E, ME>) -> Res<Self> {
        Self::new(ite, ItePos::Thn)
    }
    /// Constructor for an exploration of the else branch.
    pub fn new_els(ite: &'script hsmt::Ite<E, ME>) -> Res<Self> {
        Self::new(ite, ItePos::Els)
    }
    /// Constructor for an exploration of the otherwise branch.
    pub fn new_otw(ite: &'script hsmt::Ite<E, ME>) -> Res<Self> {
        Self::new(ite, ItePos::Otw)
    }
}

/// Derivative of a [`Query`].
#[derive(Debug, Clone)]
pub enum Query<'script, E, ME> {
    /// [`Block`] derivative.
    Block(Block<'script, E, ME>),
    /// [`Ite`] derivative.
    Ite(Ite<'script, E, ME>),
}
impl<'script, E, ME> Frame<'script, E, ME> for Query<'script, E, ME> {
    fn current(&self) -> Res<CurrentCmd<'script, E, ME>> {
        match self {
            Self::Block(block) => block.current(),
            Self::Ite(ite) => ite.current(),
        }
    }
}
impl<'script, E, ME> From<Block<'script, E, ME>> for Query<'script, E, ME> {
    fn from(f: Block<'script, E, ME>) -> Self {
        Self::Block(f)
    }
}
impl<'script, E, ME> From<Ite<'script, E, ME>> for Query<'script, E, ME> {
    fn from(f: Ite<'script, E, ME>) -> Self {
        Self::Ite(f)
    }
}

/// Derivative of a [`Command`].
#[derive(Debug, Clone)]
pub enum Command<'script, E, ME> {
    /// [`MLet`] derivative.
    MLet(MLet<'script>),
    /// [`Query`] derivative.
    Query(Query<'script, E, ME>),
}
impl<'script, E, ME> Frame<'script, E, ME> for Command<'script, E, ME> {
    fn current(&self) -> Res<CurrentCmd<'script, E, ME>> {
        match self {
            Self::MLet(mlet) => {
                let rhs = &mlet.mlet.rhs;
                Ok(rhs.into())
            }
            Self::Query(query) => query.current(),
        }
    }
}

impl<'script, E, ME> From<MLet<'script>> for Command<'script, E, ME> {
    fn from(f: MLet<'script>) -> Self {
        Self::MLet(f)
    }
}
impl<'script, E, ME> From<Query<'script, E, ME>> for Command<'script, E, ME> {
    fn from(f: Query<'script, E, ME>) -> Self {
        Self::Query(f)
    }
}
impl<'script, E, ME> From<Block<'script, E, ME>> for Command<'script, E, ME> {
    fn from(f: Block<'script, E, ME>) -> Self {
        Self::Query(f.into())
    }
}
impl<'script, E, ME> From<Ite<'script, E, ME>> for Command<'script, E, ME> {
    fn from(f: Ite<'script, E, ME>) -> Self {
        Self::Query(f.into())
    }
}
