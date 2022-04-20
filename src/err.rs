//! Error-handling.

prelude!();

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
    pub fn pretty(&self, style: impl crate::prelude::Style) -> String {
        match self {
            Self::Io(e) => {
                format!("{} error: {}", style.under("IO"), e)
            }
            Self::Smt(e) => {
                let mut s = format!("{} error:", style.under("smt-level"));
                for e in e.iter() {
                    s.push_str(&format!("\n- {}", e));
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
