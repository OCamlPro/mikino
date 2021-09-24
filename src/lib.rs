//! A minimal (1-)induction library.

#![forbid(missing_docs)]

pub extern crate rsmt2;

mod macros;

pub mod prelude;

pub mod check;
pub mod expr;
pub mod parse;
pub mod trans;

/// String representation of a simple demo system.
pub const DEMO: &str = r#"//! A simple demo system.
//!
//! Systems are declared in four ordered parts:
//!
//! - state variables of the system, `state`;
//! - initial predicate, `init`;
//! - transition predicate, `trans`;
//! - candidates to try to prove on the system, `candidates`.
//!
//! # Init
//!
//! The initial predicate is a constraint over the variables of the system. Any assignment of the
//! variables that makes this initial predicate true is a legal initial state.
//!
//! Say your system is just a counter with a single variable `cnt: int`. If you want to start with
//! `cnt` equal to `0`, then your initial predicate would be `cnt = 0`. If you want to start with
//! any positive value, then it would be `cnt >= 0` or `cnt ≥ 0`. If you're fine with starting with
//! any value at all, then your initial predicate can just be `true` (or `⊤`) to leave `cnt`
//! unconstrained.
//!
//! # Trans
//!
//! The transition predicate describes whether a state can be the successor of another state, or the
//! "next" state. That is, the transition predicate is a constraint that mentions variables of the
//! "current" state and variables of the "next" state. If `v` is a variable of your system, then the
//! "current" value of `v` is just written `v`. The "next" value is written `'v`.
//!
//! Going back to the simple counter system example above, you can express that the "next" value of
//! `cnt` is the current value plus one with `'cnt = cnt + 1`
//!
//! # Candidates
//!
//! A candidate is a *name* and a definition, *i.e.* a predicate over the variables of the system.
//! The name is given as a double-quoted string, for instance `"my candidate"`. The predicate is a
//! constraint over the variables. It cannot be a relation, *i.e.* mention *next-state variables*
//! like `'v`.
//!
//! In the counter system from above, maybe we want to prove that `cnt` is always positive. We can
//! do so by having a PO called, for instance, `"cnt is positive"` defined as `cnt >= 0` or `cnt ≥
//! 0`.
//!
//! # This Example
//!
//! This system is a stopwatch. It has a (time) counter `cnt`, which would be the time a real
//! stopwatch would actually display. It has two boolean variables `stop` and `reset` which would be
//! buttons on an actual stopwatch. Variable `reset` forces `cnt` to be `0` whenever it is true,
//! while `stop` freezes the value of `cnt` as long as it remains true. Note that `reset` has
//! priority over `stop`: if both are true then `cnt` will be forced to `0`.
//!
//! # Notes on Operators and Literals
//!
//! Several operators can take more than one UTF8 or ASCII form.
//!
//! - conjunction: `and`, `&&`, `∧`, `⋀`
//! - disjunction: `or` `||`, `∨`, `⋁`
//! - implication: `=>`, `⇒`, `→`, `⊃`
//! - negation: `not`, `!`, `¬`
//! - arithmetic comparison: `>`, `>=`, `≥`, `<=`, `≤`, `<`
//!
//! If-then-else-s are written Rust-style: `if <cnd> { <thn> } else { <els> }` where `<cnd>` is a
//! boolean expression, and `<thn>` and `<els>` are expressions of the same type. Rust's `else if`-s
//! are also supported: `if c_1 { t_1 } else if c_2 { t_2 } .... else { e }`.

/// Variables.
state {
    /// Stop button (input).
    stop,
    /// Reset button (input).
    reset: bool
    /// Time counter (output).
    cnt: int
}

/// Initial predicate.
init {
    // `cnt` can be anything as long as it is positive.
    cnt ≥ 0
    // if `reset`, then `cnt` has to be `0`.
    ∧ (reset ⇒ cnt = 0)
}

/// Transition predicate.
/// 
/// - `reset` has priority over `stop`;
/// - the `ite` stands for "if-then-else" and takes a condition, a `then` expression and an `else`
///   expression. These last two expressions must have the same type. In the two `ite`s below, that
///   type is always `bool`.
trans {
    if reset {
        cnt = 0
    } else if stop {
        'cnt = cnt
    } else {
        'cnt = cnt + 1
    }
}

/// Proof obligations.
candidates {
    "cnt is positive": cnt ≥ 0
    "cnt is not -7": ¬(cnt = -7)
    "if reset then cnt is 0": reset ⇒ cnt = 0
}
"#;
