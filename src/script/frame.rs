//! Frame stuff.

crate::prelude!();

use super::QueryRes;
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
pub trait Frame<'s> {
    /// Type of commands produced by this frame.
    type Output;
    /// Produces the current command.
    fn current(&self) -> Res<Self::Output>;
}

/// Derivative of a block.
#[derive(Debug, Clone)]
pub struct Block<'script, E, ME> {
    /// Original block.
    pub block: &'script hsmt::Block<E, ME>,
    /// Index of the current command in the block.
    pub current: usize,
}
impl<'script, E, ME> Frame<'script> for Block<'script, E, ME> {
    type Output = &'script hsmt::Command<E, ME>;
    fn current(&self) -> Res<Self::Output> {
        Ok(&self.block[self.current])
    }
}

impl<'script, E, ME> Block<'script, E, ME> {
    /// Constructor.
    pub fn new(block: &'script hsmt::Block<E, ME>) -> Self {
        Self { block, current: 0 }
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
impl<'script, E, ME> Frame<'script> for Ite<'script, E, ME> {
    type Output = &'script hsmt::CheckSat;
    fn current(&self) -> Res<Self::Output> {
        match self.pos {
            ItePos::Cnd => Ok(self.ite.cnd.as_ref().right().ok_or(
                "trying to access query condition of if-then-else, \
                but condition is an expression",
            )?),
            _ => todo!(),
        }
    }
}

impl<'script, E, ME> Ite<'script, E, ME> {
    /// Constructor for an exploration of the condition.
    ///
    /// Fails if the condition of the [`Ite`] is not a check sat.
    pub fn new_cnd(ite: &'script hsmt::Ite<E, ME>) -> Res<Self> {
        if ite.cnd.is_left() {
            bail!("cannot explore the condition of an if-then-else with a non-check-sat condition")
        }
        let pos = ItePos::Cnd;
        Ok(Self { ite, pos })
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
impl<'script, E, ME> Frame<'script> for Query<'script, E, ME> {
    type Output = Either<&'script hsmt::Command<E, ME>, &'script hsmt::CheckSat>;
    fn current(&self) -> Res<Self::Output> {
        match self {
            Self::Block(block) => block.current().map(Either::Left),
            Self::Ite(ite) => ite.current().map(Either::Right),
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
impl<'script, E, ME> Frame<'script> for Command<'script, E, ME> {
    type Output = Either<&'script hsmt::Command<E, ME>, &'script hsmt::CheckSat>;
    fn current(&self) -> Res<Self::Output> {
        match self {
            Self::MLet(_mlet) => bail!("[fatal] meta-let has no notion of current command"),
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