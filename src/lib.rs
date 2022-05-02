//! A minimal (1-)induction library.
//!
//! Mikino has a [binary crate][mikinobin] and a companion tutorial/introduction to formal
//! verification, [*Verification for Dummies: SMT and Induction*][dummies]. While it discusses
//! mikino mainly from the (binary-side) end-user point of view, it will be pretty useful to users
//! of the mikino API unfamiliar with (SMT-based) formal verification.
//!
//! This crate deals with two main objects: [*hsmt* scripts](#scripts) and [*hsmt* (transition)
//! systems](#transition-systems), where *hsmt* stands for **H**uman [**SMT**-LIB 2][smtlib].
//! Mikino has the ability to run scripts, and (dis)prove properties over transition systems using
//! `k`-induction. Both features are realized using [SMT solvers], see [the `solver`
//! module](solver) for more.
//!
//! Mikino only handles relatively simple SMT-LIB 2 expressions where the only types are `bool`,
//! `int` and `rat`. For details regarding the expression structures see [`expr`].
//!
//! Also, note that you will find a bunch of examples in `repository/examples` which use the
//! systems/scripts in `repository/rsc`.
//!
//! # Scripts
//!
//! An **hsmt script** is a Rust-flavored SMT-LIB 2 script, with a twist. The twist is that check
//! sat results are meta-values that users can store in *meta-variables* with `let is_sat =
//! check_sat!()`. Users can then *branch* on check sat results using `if-then-else`s. For more,
//! see
//!
//! - [`SCRIPT_DEMO`] for a description of mikino's syntax for hsmt scripts;
//! - [`parse::script`] for parsing scripts;
//! - [`script`] for running scripts;
//! - `repository/rsc/script_demo.rs` for a documented hsmt script demo.
//!
//! # Transition Systems
//!
//! An **hsmt transition system** is a declarative transition system specified with three objects:
//! - the system's *state variables*, which define the notion of *state* for the system as a
//!   valuation of all the state variables.
//! - the system's *initial predicate* or `init`, which is a predicate over the state variables
//!   (a function from a state of the system to `bool`); `init` defines the legal initial states
//!   of the system as the states for which `init(state) = true`.
//! - the system's *transition predicate* or `trans`, which is a predicate over two states `state`
//!   and `state'`; `trans` defines the states that legally follow any state `state` as all the
//!   states `state'` such that `trans(state, state') = true`.
//!
//! For more, see
//!
//! - [`TRANS_DEMO`] for a description of mikino's syntax for hsmt systems;
//! - [`parse::trans`] for parsing hsmt systems;
//! - [`trans`] for how hsmt systems are structured;
//! - [`check`] for hsmt system `k`-induction-based verification;
//! - `repository/rsc/trans_demo.rs` for a documented hsmt system demo.
//!
//! [smtlib]: https://smtlib.cs.uiowa.edu/language.shtml
//! (SMT-LIB's official website)
//! [SMT solvers]: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories
//! (SMT on wikipedia)
//! [mikinobin]: https://crates.io/crates/mikino
//! (Mikino's binary crate on crates.io)
//! [dummies]: https://ocamlpro.com/blog/2021_10_14_verification_for_dummies_smt_and_induction
//! (Induction for Dummies official)

#![forbid(missing_docs)]

pub extern crate rsmt2;

#[macro_use]
mod macros;

pub mod prelude;

pub mod ast;
pub mod check;
pub mod err;
pub mod expr;
pub mod parse;
pub mod script;
pub mod solver;
pub mod trans;

/// String representation of a simple demo system.
pub const TRANS_DEMO: &str = include_str!("../rsc/trans_demo.rs");

/// String representation of a simple demo script.
pub const SCRIPT_DEMO: &str = include_str!("../rsc/script_demo.rs");
