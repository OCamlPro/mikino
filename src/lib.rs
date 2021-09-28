//! A minimal (1-)induction library.

#![forbid(missing_docs)]

pub extern crate rsmt2;

mod macros;

pub mod prelude;

pub mod check;
pub mod expr;
pub mod parse;
pub mod trans;

/// Error-handling.
pub mod err {
    use std::fmt;

    /// Plain errors.
    #[derive(Debug)]
    pub enum Error {
        /// IO error from `std`.
        Io(std::io::Error),
        /// Error from [`rsmt2`].
        Smt(rsmt2::errors::Error),
        /// Parse error.
        Parse {
            /// Message.
            msg: String,
            /// Row where the error occurred (starts at `0`).
            row: usize,
            /// Column where the error occured (starts at `0`).
            col: usize,
            /// Line of the error.
            line: String,
            /// Previous line.
            prev: Option<String>,
            /// Next line.
            next: Option<String>,
        },
        /// A simple message.
        Msg(String),
    }
    impl Error {
        /// Parse error constructor.
        pub fn parse(
            msg: impl Into<String>,
            row: usize,
            col: usize,
            line: impl Into<String>,
            prev: Option<String>,
            next: Option<String>,
        ) -> Self {
            Self::Parse {
                msg: msg.into(),
                row,
                col,
                line: line.into(),
                prev,
                next,
            }
        }

        /// Extends an error with a chain of errors.
        pub fn extend(self, errs: impl Iterator<Item = Error>) -> ErrorChain {
            ErrorChain::from(self).extend(errs)
        }

        /// Pretty multi-line string representation.
        #[cfg(feature = "parser")]
        pub fn pretty(&self, style: impl crate::prelude::Style) -> String {
            match self {
                Self::Io(e) => {
                    format!("{} error: {}", style.under("IO"), e)
                }
                Self::Smt(e) => {
                    let mut s = format!("{} error: {}", style.under("smt-level"), e);
                    for e in e.iter() {
                        s.push_str(&format!("- {}", e));
                    }
                    s
                }
                Self::Parse {
                    msg,
                    row,
                    col,
                    line,
                    prev,
                    next,
                } => {
                    let (row, col) = (*row, *col);
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
                        "parse error at {}:{}\n{} |{}\n{} | {}",
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
                        style.red(if msg.is_empty() { "here" } else { &msg }),
                    ));
                    if let Some(next) = next {
                        s.push_str(&format!("\n{} | {}", " ".repeat(row_str.len()), next))
                    }

                    s
                }
                Self::Msg(msg) => msg.clone(),
            }
        }
    }
    impl fmt::Display for Error {
        fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::Io(e) => e.fmt(fmt),
                Self::Smt(e) => e.fmt(fmt),
                Self::Msg(e) => e.fmt(fmt),
                Self::Parse {
                    msg,
                    row,
                    col,
                    line,
                    ..
                } => {
                    write!(
                        fmt,
                        "parse error at {}:{}: {} | {}",
                        row + 1,
                        col + 1,
                        msg,
                        line
                    )
                }
            }
        }
    }
    impl From<std::io::Error> for Error {
        fn from(e: std::io::Error) -> Self {
            Self::Io(e)
        }
    }
    impl From<rsmt2::errors::Error> for Error {
        fn from(e: rsmt2::errors::Error) -> Self {
            Self::Smt(e)
        }
    }
    impl From<String> for Error {
        fn from(s: String) -> Self {
            Self::Msg(s)
        }
    }
    impl From<&str> for Error {
        fn from(s: &str) -> Self {
            Self::Msg(s.into())
        }
    }

    /// A source error and a chain of errors.
    #[derive(Debug)]
    pub struct ErrorChain {
        /// Source error.
        pub source: Error,
        /// Chain of errors on top.
        pub chain: Vec<Error>,
    }
    impl fmt::Display for ErrorChain {
        fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
            for (idx, err) in self.iter().enumerate() {
                if idx > 0 {
                    write!(fmt, ", ")?;
                }
                err.fmt(fmt)?;
            }
            Ok(())
        }
    }
    impl ErrorChain {
        /// Constructor.
        pub fn new(source: impl Into<Error>) -> Self {
            Self {
                source: source.into(),
                chain: vec![],
            }
        }

        /// Forces a new source, move the old source to the front of the chain.
        pub fn force_source(mut self, source: impl Into<Error>) -> Self {
            let mut source = source.into();
            std::mem::swap(&mut source, &mut self.source);
            self.chain.insert(0, source);
            self
        }

        /// Ref-iterator over all the errors in the chain.
        pub fn iter(&self) -> impl Iterator<Item = &Error> {
            Some(&self.source).into_iter().chain(&self.chain)
        }
        /// Own-iterator over all the errors in the chain.
        pub fn into_iter(self) -> impl Iterator<Item = Error> {
            Some(self.source).into_iter().chain(self.chain)
        }

        /// Extends the chain.
        pub fn extend(mut self, errs: impl Iterator<Item = Error>) -> Self {
            self.chain.extend(errs);
            self
        }
    }
    impl From<Error> for ErrorChain {
        fn from(source: Error) -> Self {
            Self::new(source)
        }
    }
    impl From<std::io::Error> for ErrorChain {
        fn from(e: std::io::Error) -> Self {
            Self::new(e)
        }
    }
    impl From<rsmt2::errors::Error> for ErrorChain {
        fn from(e: rsmt2::errors::Error) -> Self {
            Self::new(e)
        }
    }
    impl From<String> for ErrorChain {
        fn from(s: String) -> Self {
            Self::new(s)
        }
    }
    impl From<&str> for ErrorChain {
        fn from(s: &str) -> Self {
            Self::new(s)
        }
    }

    /// Result type.
    pub type Res<T> = Result<T, ErrorChain>;

    /// Error-chaining extension trait.
    pub trait ChainExt {
        /// Error-chaining result type.
        type Res;
        /// Chains an error.
        fn chain_err<E>(self, err: impl FnOnce() -> E) -> Self::Res
        where
            E: Into<Error>;
    }

    impl ChainExt for ErrorChain {
        type Res = ErrorChain;
        fn chain_err<E>(mut self, err: impl FnOnce() -> E) -> Self::Res
        where
            E: Into<Error>,
        {
            self.chain.push(err().into());
            self
        }
    }
    impl ChainExt for Error {
        type Res = ErrorChain;
        fn chain_err<E>(self, err: impl FnOnce() -> E) -> Self::Res
        where
            E: Into<Error>,
        {
            ErrorChain::from(self).chain_err(err)
        }
    }
    impl<T, Err> ChainExt for Result<T, Err>
    where
        Err: Into<ErrorChain>,
    {
        type Res = Res<T>;
        fn chain_err<E>(self, err: impl FnOnce() -> E) -> Self::Res
        where
            E: Into<Error>,
        {
            self.map_err(|e| e.into().chain_err(err))
        }
    }
}

/// String representation of a simple demo system, requires the `demo` feature.
#[cfg(feature = "parser")]
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
svars {
    /// Stop button (input).
    stop
    /// Reset button (input).
    reset: bool,
    /// Time counter (output).
    cnt: int,
}

/// Initial predicate.
/// 
/// Comma-separated list of stateless expressions, with optional trailing comma.
init {
    // `cnt` can be anything as long as it is positive.
    cnt ≥ 0,
    // if `reset`, then `cnt` has to be `0`.
    (reset ⇒ cnt = 0),
}

/// Transition predicate.
/// 
/// Comma-separated list of stateful expressions, with optional trailing comma.
/// 
/// - `reset` has priority over `stop`;
/// - the `ite` stands for "if-then-else" and takes a condition, a `then` expression and an `else`
///   expression. These last two expressions must have the same type. In the two `ite`s below, that
///   type is always `bool`.
trans {
    'cnt = if 'reset {
        0
    } else if 'stop {
        cnt
    } else {
        cnt + 1
    },
}

/// Proof obligations.
candidates {
    "cnt is positive": cnt ≥ 0,
    "cnt is not -7": ¬(cnt = -7),
    "if reset then cnt is 0": reset ⇒ cnt = 0,
}
"#;
