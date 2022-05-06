//! Backend parser (SMT-LIB) and frontend parser (requires the `parser` feature).

prelude!();

use expr::{Cst, Expr, Op, PExpr, SExpr, SVar, Typ, Var};
use rsmt2::parse::IdentParser;
use trans::Decls;

pub mod kw;

#[cfg(test)]
mod test;

/// A span in the input text.
#[readonly::make]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// Span's start (inclusive).
    pub start: usize,
    /// Span's end (exclusive).
    pub end: usize,
}
impl Span {
    /// Constructor.
    pub fn new(start: usize, end: usize) -> Self {
        debug_assert!(start <= end);
        Span { start, end }
    }
    /// Merges two spans, `self`'s start and `other`'s end.
    ///
    /// - illegal if `self.start > other.end`.
    pub fn merge(self, other: Self) -> Self {
        (self.start, other.end).into()
    }

    /// Extracts the relevant line of the input, and the previous/next line if any.
    pub fn pretty_of(self, text: &str) -> (Option<String>, usize, usize, String, Option<String>) {
        if text.is_empty() {
            assert_eq!(self.start, 0);
            assert_eq!(self.end, 0);
            return (None, 0, 0, "<EOI>".into(), None);
        }
        let mut lines = text.lines().enumerate();

        let mut count = self.start;
        let mut prev_line = None;

        while let Some((row, line)) = lines.next() {
            if line.len() >= count {
                let (line, next) = {
                    match lines.next().map(|(_, s)| s.to_string()) {
                        Some(next) if next.is_empty() => (line.into(), None),
                        Some(next) => (line.into(), Some(next)),
                        None if text.ends_with('\n') => (line.into(), None),
                        None => (format!("{}<EOI>", line), None),
                    }
                };
                return (prev_line.map(String::from), row, count, line, next);
            }

            count -= line.len() + 1;
            prev_line = Some(line);
        }

        panic!(
            "illegal offset {} on text of length {}",
            self.start,
            text.len()
        );
    }

    /// Pretty multi-line string representation.
    pub fn pretty_ml_of(
        self,
        text: impl AsRef<str>,
        style: impl Style,
        msg: impl AsRef<str>,
    ) -> String {
        let text = text.as_ref();
        let msg = msg.as_ref();
        let (prev, row, col, line, next) = self.pretty_of(text);
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
            "at {}:{}\n{} |{}\n{} | {}",
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
            style.red(if msg.is_empty() { "here" } else { msg }),
        ));
        if let Some(next) = next {
            s.push_str(&format!("\n{} | {}", " ".repeat(row_str.len()), next))
        }
        s
    }
}
impl From<(usize, usize)> for Span {
    fn from((start, end): (usize, usize)) -> Self {
        Self::new(start, end)
    }
}

/// Wraps something with a span.
#[derive(Debug, Clone, Copy)]
pub struct Spn<T> {
    /// Value wrapped.
    pub inner: T,
    /// Span.
    pub span: Span,
}
impl<T: PartialEq> PartialEq for Spn<T> {
    fn eq(&self, that: &Self) -> bool {
        self.inner == that.inner
    }
}
impl<T: Eq> Eq for Spn<T> {}
impl<T> Spn<T> {
    /// Constructor.
    pub fn new(inner: T, span: impl Into<Span>) -> Self {
        let span = span.into();
        Self { inner, span }
    }

    /// Applies an operation to the inner value.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spn<U> {
        Spn {
            inner: f(self.inner),
            span: self.span,
        }
    }

    /// Applies an operation yielding a result to the inner value.
    pub fn res_map<U>(
        self,
        mut f: impl FnMut(T) -> Result<U, &'static str>,
    ) -> Result<Spn<U>, &'static str> {
        let inner = f(self.inner)?;
        Ok(Spn::new(inner, self.span))
    }

    /// Unwraps `self`'s and `other`'s inner values and merges their spans.
    pub fn unwrap_merge<U>(self, other: Spn<U>) -> (T, U, Span) {
        (self.inner, other.inner, self.span.merge(other.span))
    }
}
impl<T> Deref for Spn<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.inner
    }
}
impl From<Spn<&str>> for Spn<String> {
    fn from(spn: Spn<&str>) -> Self {
        spn.map(|s| s.into())
    }
}

/// Yields `true` if `ident` is a keyword.
pub fn is_kw(ident: impl AsRef<str>) -> bool {
    kw::all.contains(ident.as_ref())
}
/// Fails if `ident` is a keyword.
pub fn fail_if_kw(ident: impl AsRef<str>) -> Result<(), String> {
    let ident = ident.as_ref();
    if is_kw(ident) {
        Err(format!("illegal use of keyword `{}`", ident))
    } else {
        Ok(())
    }
}

peg::parser! {
    /// PEG parsing rules, requires the `parser` feature.
    ///
    /// The [`crate::TRANS_DEMO`] constant illustrates and discusses the syntax expected by the
    /// parser.
    pub grammar rules() for str {
        /// Whitespace.
        pub rule whitespace() = quiet! {
            [ ' ' | '\n' | '\t' ]
        }

        /// Comment.
        ///
        /// ```rust
        /// # use mikino_api::parse::rules::comment;
        ///
        /// // Recognizes rust-style comments.
        /// assert_eq!(comment("// some comment\n"), Ok(()));
        /// assert_eq!(comment("// some comment"), Ok(()));
        ///
        /// // Rejects rust-style outer/inner comments.
        /// assert_eq!(
        ///     comment("/// outer doc comment").unwrap_err().to_string(),
        ///     "error at 1:1: expected non-documentation comment",
        /// );
        /// assert_eq!(
        ///     comment("//! outer doc comment").unwrap_err().to_string(),
        ///     "error at 1:1: expected non-documentation comment",
        /// );
        /// ```
        pub rule comment() = quiet! {
            // Rust-style.
            "//"
            // Do not match inner/outer documentation.
            &[^ '/' | '!' ]
            [^ '\n' ]*
            // Newline or EOI.
            ("\n" / ![_])
        }
        / expected!("non-documentation comment")

        /// Whitespace or comment.
        rule _() = quiet! { ( whitespace() / comment() )* }

        /// Outer comments.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::parse::rules::outer_doc;
        /// let input = "\t/// Some\n\t/// comments\n";
        /// let cmts = outer_doc(input).unwrap();
        /// assert_eq!(cmts, vec!["Some".to_string(), "comments".to_string()]);
        /// ```
        pub rule outer_doc() -> Vec<&'input str>
        = quiet! {
            (_ "///" $(" ")? line:$([^'\n']*) ("\n" / ![_]) { line })*
        }
        // / expected!("outer documentation")

        /// Inner comments.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::parse::rules::inner_doc;
        /// let input = "\t//! Some\n\t//! comments\n";
        /// let cmts = inner_doc(input).unwrap();
        /// assert_eq!(cmts, vec!["Some".to_string(), "comments".to_string()]);
        /// ```
        pub rule inner_doc() -> Vec<&'input str>
        = quiet! {
            (_ "//!" $(" ")? line:$([^'\n']*) ("\n" / ![_]) { line })*
        }
        // / expected!("inner documentation")

        /// Ident parsing.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::parse::rules::ident;
        /// // Regular idents are okay.
        /// assert_eq!(*ident("v_1").unwrap(), "v_1");
        /// assert_eq!(*ident("my_var_7").unwrap(), "my_var_7");
        ///
        /// // Cannot start with a digit.
        /// assert_eq!(
        ///     ident("0_illegal").unwrap_err().to_string(),
        ///     "error at 1:1: expected identifier",
        /// );
        ///
        /// // Cannot have weird SMT-LIB characters in unquoted identifiers.
        /// let not_legal = [
        ///     '~', '!', '@', '$', '%', '^', '&', '*',
        ///     '-', '+', '=', '<', '>', '.', '?', '/',
        /// ];
        /// let legal_ident = "v_";
        /// assert_eq!(*ident(legal_ident).unwrap(), legal_ident);
        /// for c in &not_legal {
        ///     let illegal = format!("{}{}", legal_ident, c);
        ///     assert!(ident(&illegal).is_err());
        /// }
        ///
        /// // Quoted idents can contain anything but '|' and '\'.
        /// let id = "|\n + ~ ! so free - = <> 😸 /? @^  \n\n /// |";
        /// assert_eq!(*ident(id).unwrap(), id);
        /// ```
        pub rule ident() -> Spn<&'input str>
        = quiet! {
            s:position!()
            ident:$(
                // Unquoted ident, notice it's a bit different from SMT-LIB.
                [ 'a'..='z' | 'A'..='Z' | '_' ]
                [ 'a'..='z' | 'A'..='Z' | '_' | '0'..='9' ]*
            )
            e:position!() {?
                if is_kw(ident) {
                    Err("unexpected keyword")
                } else {
                    Ok(Spn::new(ident, (s, e)))
                }
            }
            // Quoted ident.
            /
            s:position!()
            ident:$( "|" [^ '|' | '\\']* "|" )
            e:position!() {?
                if is_kw(ident) {
                    Err("unexpected keyword")
                } else {
                    Ok(Spn::new(ident, (s, e)))
                }
            }
        }
        // Error message.
        / expected!("identifier")

        /// Same as [`ident`], but allows dash (`-`) in non-leading position.
        pub rule dash_ident() -> Spn<&'input str>
        =
            start:position!() id:$(
                ident() ("-" ident())*
            ) end:position!() {
                Spn::new(id, (start, end))
            }

        /// Double-quoted string.
        pub rule dbl_quoted() -> &'input str
        = "\"" str:$( ("\\\"" / [^'"'])* ) "\"" { str }


        /// Parses boolean constants.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::parse::rules::bool;
        /// assert!(*bool("true").unwrap());
        /// assert!(*bool("⊤").unwrap());
        /// assert!(!*bool("false").unwrap());
        /// assert!(!*bool("⊥").unwrap());
        /// ```
        pub rule bool() -> Spn<bool>
        = s:position!() ("true" / "⊤") e:position!() { Spn::new(true, (s, e)) }
        / s:position!() ("false" / "⊥") e:position!() { Spn::new(false, (s, e)) }

        /// Recognizes numbers: `0` and `[1-9][0-9]*`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::parse::rules::number;
        /// let n = "0";
        /// assert_eq!(*number(n).unwrap(), n);
        /// let n = "72054324";
        /// assert_eq!(*number(n).unwrap(), n);
        pub rule number() -> Spn<&'input str>
        = s:position!() n:$("0" / ['1'..='9']['0'..='9']*) e:position!() {
            Spn::new(n, (s, e))
        }
        /// Same as [`number`] but generates an [`Int`].
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::{prelude::Int, trans::Decls, parse::rules::int_number};
        /// let n = 0;
        /// assert_eq!(*int_number(&n.to_string()).unwrap(), Int::from(n));
        /// let n = 72054324;
        /// assert_eq!(*int_number(&n.to_string()).unwrap(), Int::from(n));
        pub rule int_number() -> Spn<Int>
        = digits:number() {?
            digits.res_map(|digits|
                Int::parse_bytes(digits.as_bytes(), 10)
                    .ok_or("illegal unsigned integer")
            )
        }

        /// Parses an unsigned [`Int`], cannot be followed by a `.`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::{parse::rules::uint, prelude::Int};
        /// let n = 0;
        /// assert_eq!(*uint(&n.to_string()).unwrap(), Int::from(n));
        /// let n = 72054324;
        /// assert_eq!(*uint(&n.to_string()).unwrap(), Int::from(n));
        ///
        /// // Cannot be followed by a `.`.
        /// let n = "72054324.";
        /// assert_eq!(
        ///     uint(n).unwrap_err().to_string(),
        ///     "error at 1:1: expected integer"
        /// );
        /// ```
        pub rule uint() -> Spn<Int>
        = quiet! {
            res:int_number() !['.'] { res }
        }
        / expected!("integer")

        /// Parses an isize.
        pub rule isize() -> isize
        = quiet! {
            sign:("-" _)? code:number() {?
                let neg = sign.is_some();
                isize::from_str_radix(code.inner, 10)
                    .map(|i|
                        if neg {
                            - i
                        } else {
                            i
                        }
                    ).map_err(|e|
                        "illegal `isize` value"
                    )
            }
        }
        / expected!("isize value")


        /// Parses an unsigned [`Int`], cannot be followed by a `.`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::{parse::rules::decimal, prelude::{Int, Rat}};
        /// let n = 0.0;
        /// # println!("{:.0}.", n);
        /// assert_eq!(*decimal(&format!("{:.0}.", n)).unwrap(), Rat::from_float(n).unwrap());
        /// # println!("{:.1}", n);
        /// assert_eq!(*decimal(&format!("{:.1}", n)).unwrap(), Rat::from_float(n).unwrap());
        /// # println!("{:.7}", n);
        /// assert_eq!(*decimal(&format!("{:.7}", n)).unwrap(), Rat::from_float(n).unwrap());
        /// let n = 546205420374.0;
        /// # println!("{:.0}.", n);
        /// assert_eq!(*decimal(&format!("{:.0}.", n)).unwrap(), Rat::from_float(n).unwrap());
        /// # println!("{:.1}", n);
        /// assert_eq!(*decimal(&format!("{:.1}", n)).unwrap(), Rat::from_float(n).unwrap());
        /// # println!("{:.7}", n);
        /// assert_eq!(*decimal(&format!("{:.7}", n)).unwrap(), Rat::from_float(n).unwrap());
        /// let n = 72054324.54205;
        /// # println!("{}", n);
        /// assert_eq!(
        ///     *decimal(&format!("{}", n)).unwrap(),
        ///     Rat::new((7205432454205 as u64).into(), 100000.into()),
        /// );
        /// # println!("{}00000000", n);
        /// assert_eq!(
        ///     *decimal(&format!("{}00000000", n)).unwrap(),
        ///     Rat::new((7205432454205 as u64).into(), 100000.into()),
        /// );
        /// ```
        pub rule decimal() -> Spn<Rat>
        = quiet! {
            s:position!()
            n:int_number()
            "."
            d:$(['0'..='9']*)
            e:position!() {?
                let n = n.inner;
                let mut numer = n;
                let mut denom = Int::one();
                if !d.is_empty() {
                    let d_len = d.len();
                    let d = Int::parse_bytes(d.as_bytes(), 10).ok_or("illegal decimal")?;
                    for _ in 0..d_len {
                        numer = numer * 10;
                        denom = denom * 10;
                    }
                    numer = numer + d;
                }
                let rat = Rat::new(numer, denom);

                Ok(Spn::new(rat, (s, e)))
            }
        }
        / expected!("decimal number")

        /// Parses constants.
        pub rule cst() -> Spn<Cst>
        = quiet! {
            rat:decimal() {
                rat.map(Cst::R)
            }
            / int:uint() {
                int.map(Cst::I)
            }
            / b:bool() {
                b.map(Cst::B)
            }
        }
        / expected!("int/rat/bool constant")

        /// Parses variables.
        pub rule hsmt_var() -> ast::Expr<'input>
        = quiet! {
            prime:(
                ps:position!() "'" pe:position!() {
                    Span::from((ps, pe))
                }
            )? var:ident() {
                ast::Expr::svar(var, prime)
            }
        }
        / expected!("(un)primed state variable")

        /// Parses an if-then-else.
        ///
        /// No parens needed, for documentation see [`hsmt_expr`].
        pub rule hsmt_ite() -> ast::Expr<'input>
        = quiet! {
            s:position!() "if" e:position!()
            _ cnd:hsmt_expr()
            _ "{"
            _ thn:hsmt_expr()
            _ "}"
            _ elseif:(
                "else" _ s:position!() "if" e:position!() _ cnd:hsmt_expr() _ "{" _ thn:hsmt_expr() _ "}" {
                    (Span::new(s, e), cnd, thn)
                }
            )*
            _ "else" _ "{"
            _ els:hsmt_expr()
            _ "}" {
                let ite = Op::Ite;
                let els = elseif.into_iter().rev().fold(
                    els,
                    |els, (if_span, cnd, thn)| ast::Expr::app(Spn::new(ite, if_span), vec![cnd, thn, els]),
                );
                ast::Expr::app(Spn::new(Op::Ite, (s,e)), vec![cnd, thn, els])
            }
        }
        / expected!("if-then-else")

        /// Parses polymorphic expressions.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::parse::rules::hsmt_expr;
        /// let ast = hsmt_expr(
        ///     "if a ⋀ n ≥ 10 { 'n = n - 1 } \
        ///     else if false { 'n > n } \
        ///     else { false }"
        /// ).unwrap();
        /// assert_eq!(
        ///     ast.to_string(),
        ///     "\
        ///         if (a ⋀ (n ≥ 10)) { \
        ///             ('n = (n - 1)) \
        ///         } else if false { \
        ///             ('n > n) \
        ///         } else { false }\
        ///     ",
        /// )
        /// ```
        ///
        /// ```rust
        /// use mikino_api::parse::rules::hsmt_expr;
        /// let ast = hsmt_expr(
        ///     "a ⋀ x ≥ 7 - m ⋁ if 7 = n + m { b_1 ⋁ b_2 } else { c }"
        /// ).unwrap();
        /// assert_eq!(
        ///     ast.to_string(),
        ///     "\
        ///         ((a ⋀ (x ≥ (7 - m))) \
        ///         ⋁ if (7 = (n + m)) { (b_1 ⋁ b_2) } else { c })\
        ///     ",
        /// )
        /// ```
        pub rule hsmt_expr() -> ast::Expr<'input>
        = ast:precedence! {
            // Implication, right associative.
            lft:@ _ s:position!() (
                "=>" / "⇒" / "→" / "⊃"
             ) e:position!() _ rgt:(@) {
                ast::Expr::binapp(Spn::new(Op::Implies, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() (
                "∨" / "⋁" / "||" / "or"
             ) e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Or, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() (
                "∧" / "⋀" / "&&" / "and"
            ) e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::And, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() "<" e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Lt, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() ("<=" / "≤") e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Le, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() (">=" / "≥") e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Ge, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() ">" e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Gt, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() "=" e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Eq, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() "+" e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Add, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() "-" e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Sub, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() "%" e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Mod, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() "*" e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Mul, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() "/" e:position!() _ rgt:@ {
                ast::Expr::binapp(Spn::new(Op::Div, (s, e)), lft, rgt)
            }
            --
            s:position!() ("¬" / "!" / "not") e:position!() _ arg:@ {
                ast::Expr::unapp(Spn::new(Op::Not, (s, e)), arg)
            }
            s:position!() "-" e:position!() _ arg:@ {
                ast::Expr::unapp(Spn::new(Op::Sub, (s, e)), arg)
            }
            --
            ite:hsmt_ite() {
                ite
            }
            var:hsmt_var() {
                var
            }
            cst:cst() {
                ast::Expr::cst(cst)
            }
            "(" _ e:hsmt_expr() _ ")" {
                let mut e = e;
                e.close();
                e
            }
        }

        /// Same as [`hsmt_expr`].
        pub rule hsmt_expr_with_repr() -> (ast::Expr<'input>, String)
        = repr:&($(hsmt_expr())) expr:hsmt_expr() {
            (expr, repr.into())
        }

        /// Parses a type.
        ///
        /// Can be `int`, `rat`, or `bool`.
        pub rule hsmt_typ() -> expr::Typ
        = quiet! {
            "int" { expr::Typ::Int }
            / "rat" { expr::Typ::Rat }
            / "bool" { expr::Typ::Bool }
        }
        / expected!("a type (`int`, `rat` or `bool`")

        /// Parses some state variables.
        ///
        /// A state declaration is a comma-separated list of `<ident> : <type>`, with an optional
        /// trailing comma. For convenience, state variables with the same type can be listed
        /// together, separated by whitespace(s), before the `: <type>`. For instance, `v_1 v_2 v_3:
        /// int`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::parse::rules::svars;
        /// let input = "\
        ///     n_1 : int,
        ///     b_1 : bool,
        ///     // Avoid putting declarations on the same line, it looks bad.
        ///     n_2: int, b_2 : bool,
        ///     // Aggregated declaration.
        ///     n_3 n_4 n_5: int,
        ///     p q: bool,\
        /// ";
        /// let decls = svars(input).unwrap().unwrap();
        /// assert_eq!(
        ///     decls.to_string(),
        ///     // State-declaration-printing sorts and aggregates idents alphabetically.
        ///     "\
        /// b_1 b_2: bool,
        /// n_1 n_2 n_3 n_4 n_5: int,
        /// p q: bool,\
        ///     "
        /// );
        /// ```
        pub rule svars() -> PRes<trans::Decls>
        = svars:(
            quiet! {
                _
                svar_doc:outer_doc()
                _
                svar:ident()
                svars:(
                    _
                    svar_doc:outer_doc()
                    _ id:ident() {
                        id
                    }
                )*
                _ ":" _ svars_typ:hsmt_typ()
                {
                    (svar, svars, svars_typ)
                }
            }
            / expected!(r#"list of "<ident>, <ident>, ... : <type>""#)
        ) ++ (_ "," _) (",")? {
            let mut decls = trans::Decls::new();
            for (svar, svars, typ) in svars {
                for svar in Some(svar).into_iter().chain(svars) {
                    let prev = decls.register(svar.inner, typ);
                    if prev.is_some() {
                        return Err(PError::new(
                            format!("variable `{}` is already declared", svar.inner),
                            svar.span
                        ));
                    }
                }
            }
            Ok(decls)
        }

        /// Parses some candidates.
        ///
        /// Accepts a list of name/expression pairs of the form `<name> : <expr>` (no separator).
        /// Names are double-quoted `"..."` strings and must all be distinct. Expressions have to
        /// be stateless (no `'` prime).
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::parse::rules::candidates;
        /// let input = r#"
        ///     "some candidate": x ≥ 0,
        ///     "another one": x ≥ y + 2 ⋁ y ≥ -7,
        ///     "tautology": p ⋁ ¬p,"#;
        /// let mut candidates = candidates(input).unwrap().into_iter();
        ///
        /// let (name, expr) = candidates.next().unwrap();
        /// assert_eq!(*name, "some candidate");
        /// assert_eq!(expr.to_string(), "(x ≥ 0)");
        ///
        /// let (name, expr) = candidates.next().unwrap();
        /// assert_eq!(*name, "another one");
        /// assert_eq!(expr.to_string(), "((x ≥ (y + 2)) ⋁ (y ≥ (-7)))");
        ///
        /// let (name, expr) = candidates.next().unwrap();
        /// assert_eq!(*name, "tautology");
        /// assert_eq!(expr.to_string(), "(p ⋁ (¬p))");
        /// ```
        pub rule candidates() -> Vec<(Spn<&'input str>, ast::Expr<'input>)>
        = quiet! {
            cands:(
                _ s:position!() name:dbl_quoted() e:position!() _ ":" _
                expr:hsmt_expr()
                {
                    (Spn::new(name, (s, e)), expr)
                }
            ) ++ (_ "," _) (",")? {
                cands
            }
        }
        / expected!(r#"list of "<name> : <expr>" where <name> is a double-quoted string"#)

        /// Parses a full instance.
        ///
        /// Same documentation as [the `trans` function][crate::parse::trans].
        pub rule hsmt_trans() -> PRes<trans::Sys>
        =
        sys_doc:inner_doc()

        vars_doc:outer_doc()
        _ "svars" _ "{" _ decls:svars() _ "}"
        init_doc:outer_doc()
        _ init_s:position!() "init" init_e:position!() _ "{" _ hsmt_init:(
            quiet! {
                init:(hsmt_expr()) ++ (_ "," _) (",")? { init }
            }
            / expected!("comma-separated list of stateless expressions")
         ) _  "}"
        trans_doc:outer_doc()
        _ trans_s:position!() "trans" trans_e:position!() _ "{" _ hsmt_trans:(
            quiet! {
                trans:(hsmt_expr()) ++ (_ "," _) (",")? { trans }
            }
            / expected!("comma-separated list of stateful expressions")
         ) _ "}"
        candidates_doc:outer_doc()
        _ "candidates" _ "{" _ candidates:candidates() _ "}"
        _ {
            let decls = decls?;
            let init = ast::Expr::app(Spn::new(Op::And, (init_s, init_e)), hsmt_init).to_expr(&decls)?;
            let trans = ast::Expr::app(Spn::new(Op::And, (trans_s, trans_e)), hsmt_trans).to_sexpr(&decls)?;

            let mut pos = Map::new();

            for (name, expr) in candidates {
                let candidate = expr.to_expr(&decls).map_err(|e| e.chain_err(|| format!("in candidate `{}`", name.inner)))?;
                let prev =  pos.insert(name.inner.to_string(), candidate);
                if prev.is_some() {
                    return Err(PError::new("a candidate with this name is already defined", name.span))
                }
            }

            Ok(trans::Sys::new(decls, init, trans, pos))
        }








        /// A **non-empty** sequence of commands.
        pub rule commands() -> PRes<ast::script::Commands<ast::Expr<'input>, ast::Expr<'input>>>
        =
            head:command() tail:(_ cmd:command() { cmd })* {
                let mut cmds = Vec::with_capacity(tail.len());
                cmds.push(head?);
                for cmd in tail {
                    cmds.push(cmd?);
                }
                Ok(cmds)
            }

        /// Command parser.
        pub rule command() -> PRes<ast::script::Command<ast::Expr<'input>, ast::Expr<'input>>>
        =
            odoc:outer_doc() _ res:(
                cmd:set_options() { Ok(cmd?.into()) }
                /
                cmd:const_decls() { Ok(cmd?.into()) }
                /
                cmd:mlet() { Ok(cmd?.into()) }
                /
                cmd:assert() { Ok(cmd?.into()) }
                /
                cmd:get_model() { Ok(cmd?.into()) }
                /
                cmd:get_values() { Ok(cmd?.into()) }
                /
                cmd:echo() { Ok(cmd?.into()) }
                /
                cmd:reset() { Ok(cmd?.into()) }
                /
                query:query() { Ok(query?.into()) }
            ) {
                res
            }

        /// Query parser.
        pub rule query() -> PRes<ast::script::Query<ast::Expr<'input>, ast::Expr<'input>>>
        =
            q:block() { Ok(q?.into()) }
            /
            q:check_sat() { Ok(q?.into()) }
            /
            q:ite() { Ok(q?.into()) }
            /
            q:panic() { Ok(q?.into()) }
            /
            q:exit() { Ok(q?.into()) }






        /// Block parser.
        pub rule block() -> PRes<ast::script::Block<ast::Expr<'input>, ast::Expr<'input>>>
        =
            "{" commands:(_ cmd:command() { cmd })* _ "}" {
                let mut content = Vec::with_capacity(commands.len());
                for command in commands {
                    content.push(command?)
                }
                Ok(ast::script::Block::new(content))
            }

        /// Check sat.
        pub rule check_sat() -> PRes<ast::script::CheckSat>
        =
            start:position!() "check_sat" "!"? end:position!()
            _ "("
                // (_ key:$(ident()) _ ":" _ ""
            _ ")" {
                Ok(ast::script::CheckSat::new((start, end), None, None))
            }
            /
            start:position!() "check_sat" "!"? end:position!()
            _ "{"
                // (_ key:$(ident()) _ ":" _ ""
            _ "}" {
                Ok(ast::script::CheckSat::new((start, end), None, None))
            }

        /// Ite.
        pub rule ite() -> PRes<ast::script::Ite<ast::Expr<'input>, ast::Expr<'input>>>
        =
            start:position!() "if" end:position!()
            _ cnd:(
                cnd:check_sat() { cnd.map(Either::Right) }
                /
                cnd:ident() {
                    let cnd = cnd.map(expr::MetaVar::new);
                    Ok(Either::Left(cnd))
                }
            ) _ thn:block()
            tail:(
                // Else branch
                _ "else" _ els:block()
                // Otherwise branch (timeout/unknown)
                otw:(
                    _ "otherwise" _ otw:block() { otw }
                )? {
                    (els, otw)
                }
            )? {
                let (els, otw) = tail.unwrap_or_else(
                    || (Ok(ast::script::Block::new(vec![])), None)
                );
                let otw = if let Some(otw) = otw {
                    Some(otw?)
                } else {
                    None
                };
                Ok(ast::script::Ite::new((start, end), cnd?, thn?, els?, otw))
            }

        /// A panic.
        pub rule panic() -> PRes<ast::script::Panic>
        =
            start:position!() "panic" "!"? end:position!()
            _ "{" _ msg:dbl_quoted() _ "}" {
                Ok(ast::script::Panic::new((start, end), msg))
            }
            /
            start:position!() "panic" "!"? end:position!()
            _ "(" _ msg:dbl_quoted() _ ")" {
                Ok(ast::script::Panic::new((start, end), msg))
            }

        /// An exit.
        pub rule exit() -> PRes<ast::script::Exit>
        =
            start:position!() "exit" "!"? end:position!()
            _ "(" _ code:(isize())? _ ")" {
                Ok(ast::script::Exit::new((start, end), code))
            }




        /// A `set-option` key/value pair.
        pub rule set_option() -> ast::script::SetOption
        =
            key:dash_ident() _ ":"
            _ start:position!() val:(
                cst:cst() { Either::Left(cst.inner) }
                /
                s:dbl_quoted() { Either::Right(s.to_string()) }
            ) end:position!() {
                ast::script::SetOption::new(key, Spn::new(val, (start, end)))
            }

        /// A sequence of `set-option`s.
        pub rule set_options() -> PRes<ast::script::SetOptions>
        =
            start:position!() (
                "set_options" / "set_option"
            ) end:position!()
            _ "("
                opts:(
                    _ opt:set_option() _ { opt }
                )++"," _ ","?
            _ ")" {
                Ok(ast::script::SetOptions::new((start, end), opts))
            }

        /// A `declare-const` let-binding.
        pub rule const_decls() -> PRes<ast::script::Vars>
        =
            start:position!() "vars" end:position!()
            _ "{" _ decls:svars() _ "}" {
                Ok(ast::script::Vars::new((start, end), decls?))
            }
            / start:position!() "vars" end:position!()
            _ "(" _ decls:svars() _ ")" {
                Ok(ast::script::Vars::new((start, end), decls?))
            }

        /// A meta-binding.
        pub rule mlet() -> PRes<ast::script::MLet>
        =
            "let" _ lhs:ident() _ "=" _ query:check_sat() _ ";" {
                Ok(ast::script::MLet::new(lhs, query?))
            }

        /// An assert.
        pub rule assert() -> PRes<ast::script::Assert<ast::Expr<'input>>>
        =
            start:position!() "assert" end:position!()
            _ "{" exprs:(_ expr:hsmt_expr() _ { expr })++"," _ ","? _ "}" {
                Ok(ast::script::Assert::new((start, end), exprs))
            }
            /
            start:position!() "assert" end:position!()
            _ "(" exprs:(_ expr:hsmt_expr() _ { expr })++"," _ ","? _ ")" {
                Ok(ast::script::Assert::new((start, end), exprs))
            }

        /// An assert.
        pub rule get_model() -> PRes<ast::script::GetModel>
        =
            start:position!() token:$("get_model") "!"? end:position!() _ "(" _ ")" {
                Ok(ast::script::GetModel::new((start, end), token))
            }
            /
            start:position!() token:$("get_model") "!"? end:position!() _ "{" _ "}" {
                Ok(ast::script::GetModel::new((start, end), token))
            }

        /// An assert.
        pub rule get_values() -> PRes<ast::script::GetValues<ast::Expr<'input>>>
        =
            start:position!() token:$("get_value" "s"?/"eval") "!"? end:position!() _ "("
                _ exprs:(_ expr:hsmt_expr_with_repr() _ { expr })++"," _ ","?
            _ ")" {
                Ok(ast::script::GetValues::new((start, end), token, exprs))
            }
            /
            start:position!() token:$("get_values"/"eval") "!"? end:position!() _ "{"
                _ exprs:(_ expr:hsmt_expr_with_repr() _ { expr })++"," _ ","?
            _ "}" {
                Ok(ast::script::GetValues::new((start, end), token, exprs))
            }

        /// An assert.
        pub rule reset() -> PRes<ast::script::Reset>
        =
            start:position!() "reset" "!"? end:position!() _ "(" _ ")" {
                Ok(ast::script::Reset::new((start, end)))
            }
            /
            start:position!() "reset" "!"? end:position!() _ "{" _ "}" {
                Ok(ast::script::Reset::new((start, end)))
            }

        /// An echo.
        pub rule echo() -> PRes<ast::script::Echo>
        =
            start:position!()
                token:$("echo"/"println") "!"?
            end:position!() _ "{"
                _ msg:dbl_quoted()? _
            "}" {
                Ok(ast::script::Echo::new((start, end), token, msg))
            }
            /
            start:position!()
                token:$("echo"/"println") "!"?
            end:position!() _ "("
                _ msg:dbl_quoted()? _
            ")" {
                Ok(ast::script::Echo::new((start, end), token, msg))
            }

        /// Parses a hsmt script.
        pub rule hsmt_script() -> PRes<ast::script::Block<ast::Expr<'input>, ast::Expr<'input>>>
        =
            _ odoc:inner_doc()
            _ content:commands() _ {
                Ok(ast::script::Block::new(content?))
            }
    }
}

/// Parses a system, requires the `parser` feature.
///
/// Comments are one-line rust-style: `// ..\n`.
///
/// A system is composed of four `{ ... }` blocks each starting with a specific keyword:
///
/// - `svars { ... }`: the [state variables][rules::svars] of the system;
///
/// - `init { ... }`: the initial predicate, *i.e.* a stateless (no `'` prime) expression;
///
/// - `trans { ... }`: the transition relation, *i.e.* a stateful (`'` primes allowed) expression;
///
/// - `candidates { ... }`: some [candidates][rules::candidates] to prove over the systems.
pub fn trans(txt: &str) -> Res<trans::Sys> {
    let res: Res<trans::Sys> = match rules::hsmt_trans(txt) {
        Ok(res) => res.map_err(|e| e.into_error(txt)),
        Err(e) => {
            // println!("peg parse error");
            let span = Span::new(e.location.offset, e.location.offset);
            let (prev, row, col, line, next) = span.pretty_of(txt);
            let err = Error::parse("", row, col, line, prev, next);
            Err(err.chain_err(|| format!("expected {}", e.expected)))
        }
    };
    res.chain_err(|| "run mikino in 'demo' mode for more details about the syntax")
}

/// Parses a system, requires the `parser` feature.
///
/// Comments are one-line rust-style: `// ..\n`.
///
/// A system is composed of four `{ ... }` blocks each starting with a specific keyword:
///
/// - `svars { ... }`: the [state variables][rules::svars] of the system;
///
/// - `init { ... }`: the initial predicate, *i.e.* a stateless (no `'` prime) expression;
///
/// - `trans { ... }`: the transition relation, *i.e.* a stateful (`'` primes allowed) expression;
///
/// - `candidates { ... }`: some [candidates][rules::candidates] to prove over the systems.
pub fn script(txt: &str) -> Res<ast::script::Block<ast::Expr, ast::Expr>> {
    let res: Res<_> = match rules::hsmt_script(txt) {
        Ok(res) => res.map_err(|e| e.into_error(txt)),
        Err(e) => {
            // println!("peg parse error");
            let span = Span::new(e.location.offset, e.location.offset);
            let (prev, row, col, line, next) = span.pretty_of(txt);
            let err = Error::parse("", row, col, line, prev, next);
            Err(err.chain_err(|| format!("expected {}", e.expected)))
        }
    };
    res.chain_err(|| "run mikino in 'demo' mode for more details about the syntax")
}

/// Parses its input text.
pub struct Parser<'txt> {
    /// Text to parse.
    txt: &'txt str,
    /// Position in the text.
    cursor: usize,
    /// Declarations accumulated so far.
    decls: Decls,
}
impl<'txt> Parser<'txt> {
    /// Constructor.
    pub fn new(txt: &'txt str) -> Self {
        Self {
            txt,
            cursor: 0,
            decls: Decls::new(),
        }
    }

    /// Backtracks to a position.
    fn backtrack(&mut self, pos: usize) {
        self.cursor = pos
    }

    /// Fails at some position.
    pub fn fail_at(&self, pos: usize, msg: impl Into<String>) -> Error {
        let (prev, row, col, line, next) = Span::new(pos, pos).pretty_of(self.txt);
        Error::Parse {
            msg: msg.into(),
            prev,
            row,
            col,
            line,
            next,
        }
    }

    /// Fails at the current position.
    pub fn fail(&self, msg: impl Into<String>) -> Error {
        self.fail_at(self.cursor, msg)
    }

    /// Extracts the line, line index and column char-index (**not bytes**) of a position.
    ///
    /// Notes:
    ///
    /// - tabs `'\t'` are transformed into four spaces `    `, which the column index accounts for;
    /// - line and column indices **start from `0`**;
    /// - line might contain unicode characters, be careful of the column index.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::Parser};
    /// let mut parser = Parser::new("\nsome text\n\t\th");
    /// let (line, col, row) = parser.pretty_pos(13).unwrap();
    /// # println!("line: `{}`, col: {}, row: {}", line, col, row);
    /// assert_ne!(line, "\t\th");
    /// assert_eq!(line, "        h");
    /// assert_eq!(col, 2);
    /// assert_eq!(row, 8);
    /// assert_eq!(line.as_bytes()[8], b'h');
    /// ```
    pub fn pretty_pos(&self, pos: usize) -> Res<(String, usize, usize)> {
        let (mut curr, mut row) = (0, 0);
        for line in self.txt.lines() {
            if curr + line.len() + 1 < pos {
                curr += line.len() + 1;
                row += 1;
                if curr >= self.txt.len() {
                    break;
                }
            } else {
                let col = line
                    .chars()
                    .take(pos - curr)
                    .fold(0, |acc, n| acc + if n == '\t' { 4 } else { 1 });
                let mut actual_line = String::new();
                for c in line.chars() {
                    if c == '\t' {
                        actual_line.push_str("    ");
                    } else {
                        actual_line.push(c);
                    }
                }
                return Ok((actual_line, row, col));
            }
        }
        bail!(
            "cannot extract row/col information from position {}, position is out of range",
            pos
        )
    }

    /// Declaration accessor.
    pub fn get_decls(&self) -> &Decls {
        &self.decls
    }

    /// True if there is no more text to parse.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "some stuff";
    /// let mut parser = Parser::new(txt);
    /// parser.parse_until(|_| false, true);
    /// assert_eq!(parser.rest(), "");
    /// assert!(parser.is_at_eoi())
    /// ```
    pub fn is_at_eoi(&self) -> bool {
        self.cursor >= self.txt.len()
    }

    /// The text left to parse.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "some stuff";
    /// let mut parser = Parser::new(txt);
    /// parser.parse_until(char::is_whitespace, true);
    /// assert_eq!(parser.rest(), "stuff")
    /// ```
    pub fn rest(&self) -> &'txt str {
        &self.txt[self.cursor..]
    }

    /// Pretty version of the text left to parse.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "some stuff\non several\n// lines";
    /// let mut parser = Parser::new(txt);
    /// parser.parse_until(char::is_whitespace, true);
    /// assert_eq!(
    ///     parser.pretty_rest(),
    ///     "| `stuff`\n| `on several`\n| `// lines`"
    /// )
    /// ```
    pub fn pretty_rest(&self) -> String {
        let mut s = String::new();
        for (index, line) in self.rest().lines().enumerate() {
            if index > 0 {
                s.push_str("\n")
            }
            s.push_str("| `");
            s.push_str(line);
            s.push_str("`")
        }
        s
    }

    /// Parses some whitespaces.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = " \n\n  \r token";
    /// let mut parser = Parser::new(txt);
    /// parser.ws();
    /// assert_eq!(parser.rest(), "token")
    /// ```
    pub fn ws(&mut self) -> bool {
        let mut changed = false;
        if self.cursor < self.txt.len() {
            for c in self.txt[self.cursor..].chars() {
                if c.is_whitespace() {
                    changed = true;
                    self.cursor += c.len_utf8()
                } else {
                    break;
                }
            }
        }
        changed
    }

    /// Parses a comment.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "// a single line comment\n  some more stuff";
    /// let mut parser = Parser::new(txt);
    /// parser.cmt();
    /// assert_eq!(parser.rest(), "  some more stuff")
    /// ```
    pub fn cmt(&mut self) -> bool {
        if self.cursor >= self.txt.len() {
            return false;
        }
        let mut chars = self.txt[self.cursor..].chars();
        if chars.next() != Some('/') || chars.next() != Some('/') {
            return false;
        }
        self.cursor += 2 * '/'.len_utf8();
        let _ = self.parse_until(|c| c == '\n' || c == '\r', true);
        true
    }

    /// Consumes all comments and whitespaces from the current position.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "  \n  // A comment // nested\n   \r // comment\n  some stuff";
    /// let mut parser = Parser::new(txt);
    /// parser.ws_cmt();
    /// assert_eq!(parser.rest(), "some stuff")
    /// ```
    pub fn ws_cmt(&mut self) {
        loop {
            let ws = self.ws();
            let cmt = self.cmt();
            if !ws && !cmt {
                break;
            }
        }
    }

    /// Consumes characters until some predicate is true or we reach EOI.
    ///
    /// Boolean flag `inclusive` specifies whether the first character `c` on which `stop(c)` is
    /// true should be parsed true or not.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "some stuff: followed by more things";
    /// let mut parser = Parser::new(txt);
    /// parser.parse_until(char::is_whitespace, true);
    /// assert_eq!(parser.rest(), "stuff: followed by more things");
    /// parser.parse_until(|c| c == ':', false);
    /// assert_eq!(parser.rest(), ": followed by more things");
    /// let mut parser = Parser::new(txt);
    /// parser.parse_until(|c| c == 'b', false);
    /// assert_eq!(parser.rest(), "by more things")
    /// ```
    pub fn parse_until<F: Fn(char) -> bool>(&mut self, stop: F, inclusive: bool) -> &'txt str {
        if self.cursor >= self.txt.len() {
            return &self.txt[0..0];
        }
        let start = self.cursor;
        let mut chars = self.txt[self.cursor..].chars();
        while let Some(c) = chars.next() {
            if stop(c) {
                if inclusive {
                    self.cursor += c.len_utf8()
                }
                break;
            } else {
                self.cursor += c.len_utf8()
            }
        }
        &self.txt[start..self.cursor]
    }

    /// Tries to parse a tag.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "some stuff: followed by more things";
    /// let mut parser = Parser::new(txt);
    /// assert!(parser.try_tag("some"));
    /// assert!(!parser.try_tag("stuff"));
    /// parser.ws_cmt();
    /// assert!(parser.try_tag("stuff: "));
    /// assert!(parser.try_tag("followed by more things"))
    /// ```
    pub fn try_tag(&mut self, tag: &str) -> bool {
        if self.cursor >= self.txt.len() {
            false
        } else {
            let mut chars = self.txt[self.cursor..].chars();
            for c in tag.chars() {
                let next = chars.next();
                if Some(c) != next {
                    return false;
                }
            }
            self.cursor += tag.len();
            true
        }
    }
    /// Parses a tag or fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "some stuff: followed by more things";
    /// let mut parser = Parser::new(txt);
    /// assert!(parser.tag("some").is_ok());
    /// assert!(parser.tag("stuff").is_err());
    /// parser.ws_cmt();
    /// assert!(parser.tag("stuff: ").is_ok());
    /// assert!(parser.tag("followed by more things").is_ok())
    /// ```
    pub fn tag(&mut self, tag: &str) -> Res<()> {
        if self.try_tag(tag) {
            Ok(())
        } else {
            bail!(self.fail(format!("expected token `{}`", tag)))
        }
    }

    /// Tries to parse an identifier.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "my_identifier 470not_an_identifier legal_id";
    /// let mut parser = Parser::new(txt);
    /// assert_eq!(parser.try_id().unwrap(), "my_identifier");
    /// parser.ws_cmt();
    /// assert!(parser.try_id().is_none());
    /// parser.parse_until(char::is_whitespace, true);
    /// assert_eq!(parser.try_id().unwrap(), "legal_id");
    /// ```
    pub fn try_id(&mut self) -> Option<&'txt str> {
        if self.cursor >= self.txt.len() {
            return None;
        }

        let start = self.cursor;
        let mut chars = self.txt[self.cursor..].chars();
        if let Some(c) = chars.next() {
            if c.is_alphabetic() || c == '_' {
                self.cursor += c.len_utf8()
            } else {
                return None;
            }
        }
        let _ = self.parse_until(|c| !c.is_alphanumeric() && c != '_', false);
        Some(&self.txt[start..self.cursor])
    }

    /// Parses an identifier.
    pub fn id(&mut self) -> Res<&'txt str> {
        self.try_id()
            .ok_or_else(|| self.fail("expected an identifier").into())
    }

    /// Tries to parse an integer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "integer: 72 and more tokens";
    /// # println!("txt: `{}`", txt);
    /// let mut parser = Parser::new(txt);
    /// # println!("running `parse_until`");
    /// let _ = parser.parse_until(char::is_whitespace, true);
    /// # println!("running `try_int`\n{}", parser.pretty_rest());
    /// let int = parser.try_int().unwrap();
    /// assert_eq! { &int.to_string(), "72" }
    /// ```
    pub fn try_int(&mut self) -> Option<Int> {
        let start = self.cursor;
        macro_rules! abort {
            () => {{
                self.backtrack(start);
                return None;
            }};
        }

        let neg = if self.try_tag("(") {
            self.ws_cmt();
            if self.try_tag("-") {
                self.ws_cmt();
                true
            } else {
                abort!()
            }
        } else {
            false
        };

        let int = self.parse_until(|c| !c.is_numeric(), false);
        if int.len() > 0 {
            let mut int =
                Int::parse_bytes(int.as_bytes(), 10).expect("parsing an integer cannot fail");
            if neg {
                self.ws_cmt();
                if !self.try_tag(")") {
                    abort!()
                }
                int = -int
            }
            Some(int)
        } else {
            abort!()
        }
    }

    /// Tries to parse a rational.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "integer: (/ 72 11) and more tokens";
    /// # println!("txt: `{}`", txt);
    /// let mut parser = Parser::new(txt);
    /// # println!("running `parse_until`");
    /// let _ = parser.parse_until(char::is_whitespace, true);
    /// # println!("running `try_rat`\n{}", parser.pretty_rest());
    /// let rat = parser.try_rat().unwrap().unwrap();
    /// assert_eq! { &rat.to_string(), "72/11" }
    /// ```
    pub fn try_rat(&mut self) -> Res<Option<Rat>> {
        let start = self.cursor;
        macro_rules! abort {
            () => {{
                self.backtrack(start);
                return Ok(None);
            }};
            (if !$e:expr) => {{
                if !$e {
                    abort!()
                }
            }};
            (if not let Some(_) = $e:expr) => {{
                if let Some(res) = $e {
                    res
                } else {
                    abort!()
                }
            }};
        }

        abort!(if !self.try_tag("("));
        self.ws_cmt();

        let negated = if self.try_tag("-") {
            self.ws_cmt();
            abort!(if !self.try_tag("("));
            self.ws_cmt();
            true
        } else {
            false
        };

        abort!(if !self.try_tag("/"));
        self.ws_cmt();

        let num = abort!(if not let Some(_) = self.try_int());
        self.ws_cmt();
        let den = abort!(if not let Some(_) = self.try_int());
        self.ws_cmt();
        self.tag(")")?;

        if den.is_zero() {
            bail!(self.fail("division by zero"))
        }

        let mut rat = Rat::new(num, den);
        if negated {
            self.ws_cmt();
            abort!(if !self.try_tag(")"));
            rat = -rat
        }
        Ok(Some(rat))
    }

    /// Tries to parse a boolean.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// let txt = "some noise:true   // comments\nfalse";
    /// # println!("txt: `{}`", txt);
    /// let mut parser = Parser::new(txt);
    /// # println!("running `parse_until`");
    /// let _ = parser.parse_until(|c| c == ':', true);
    /// # println!("running `try_bool`\n{}", parser.pretty_rest());
    /// let bool = parser.try_bool().unwrap();
    /// assert!(bool);
    /// # println!("ws_cmt");
    /// parser.ws_cmt();
    /// # println!("running `try_bool`\n{}", parser.pretty_rest());
    /// let bool = parser.try_bool().unwrap();
    /// assert!(!bool)
    /// ```
    pub fn try_bool(&mut self) -> Option<bool> {
        if self.try_tag("true") {
            Some(true)
        } else if self.try_tag("false") {
            Some(false)
        } else {
            None
        }
    }

    /// Tries to parse a constant.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use mikino_api::{trans::Decls, parse::*};
    /// # use mikino_api::expr::*;
    /// let txt = "7405,(/ 7 103),false";
    /// let mut parser = Parser::new(txt);
    /// assert_eq!(parser.try_cst().unwrap().unwrap(), 7405.into());
    /// parser.tag(",").unwrap();
    /// assert_eq!(parser.try_cst().unwrap().unwrap(), (7, 103).into());
    /// parser.tag(",").unwrap();
    /// assert_eq!(parser.try_cst().unwrap().unwrap(), false.into());
    /// ```
    pub fn try_cst(&mut self) -> Res<Option<Cst>> {
        if let Some(b) = self.try_bool() {
            Ok(Some(Cst::B(b)))
        } else if let Some(i) = self.try_int() {
            Ok(Some(Cst::I(i)))
        } else if let Some(r) = self.try_rat()? {
            Ok(Some(Cst::R(r)))
        } else {
            Ok(None)
        }
    }

    /// Parses a type.
    pub fn typ(&mut self) -> Res<Typ> {
        if self.try_tag("bool") {
            Ok(Typ::Bool)
        } else if self.try_tag("int") {
            Ok(Typ::Int)
        } else if self.try_tag("rat") {
            Ok(Typ::Rat)
        } else {
            bail!(self.fail("expected type"))
        }
    }

    /// Tries to parse a variable.
    pub fn try_abstract_var<T>(
        &mut self,
        and_then: impl Fn(&Decls, &str) -> Option<T>,
    ) -> Res<Option<T>> {
        let start = self.cursor;
        if let Some(id) = self.try_id() {
            if let Some(res) = and_then(&mut self.decls, id) {
                Ok(Some(res))
            } else {
                bail!(self.fail_at(start, format!("unknown variable `{}`", id)))
            }
        } else {
            Ok(None)
        }
    }

    /// Tries to parse a stateless variable.
    pub fn try_var(&mut self) -> Res<Option<Var>> {
        self.try_abstract_var(|decls, id| decls.get_var(id))
    }

    /// Tries to parse a stateful variable.
    pub fn try_svar(&mut self) -> Res<Option<SVar>> {
        if let Some(svar) = self.try_abstract_var(|decls, id| decls.get_next_var(id))? {
            return Ok(Some(svar));
        }

        let start = self.cursor;
        macro_rules! abort {
            () => {{
                self.backtrack(start);
                return Ok(None);
            }};
            (if !$e:expr) => {{
                if !$e {
                    abort!()
                }
            }};
            (if not let Some(_) = $e:expr) => {{
                if let Some(res) = $e {
                    res
                } else {
                    abort!()
                }
            }};
        }

        abort!(if !self.try_tag("("));
        self.ws_cmt();
        abort!(if !self.try_tag("pre"));
        self.ws_cmt();
        let svar = abort!(
            if not let Some(_) = self.try_abstract_var(|decls, id| decls.get_curr_var(id))?
        );
        self.ws_cmt();
        self.tag(")")
            .chain_err(|| "closing application of `pre` operator")?;
        Ok(Some(svar))
    }

    /// Parse an operator.
    pub fn op(&mut self) -> Res<Op> {
        let start = self.cursor;
        let op = self.parse_until(char::is_whitespace, false);
        if let Some(op) = Op::of_str(op) {
            Ok(op)
        } else if op == "pre" {
            bail!(self.fail_at(start, "illegal `pre` operator in stateless expression"))
        } else {
            bail!(self.fail_at(start, format!("unknown operator `{}`", op)))
        }
    }

    /// Parses a stateless expression.
    pub fn expr(&mut self) -> Res<Expr> {
        self.pexpr(Self::try_var)
    }
    /// Parses a stateful expression.
    pub fn sexpr(&mut self) -> Res<SExpr> {
        self.pexpr(Self::try_svar)
    }

    /// Parses a stateless/stateful expression.
    ///
    /// Stackless.
    pub fn pexpr<V>(&mut self, parse_var: impl Fn(&mut Self) -> Res<Option<V>>) -> Res<PExpr<V>>
    where
        V: HasTyp,
    {
        let mut stack: Vec<(Op, Vec<PExpr<V>>)> = vec![];

        'go_down_applications: loop {
            let mut expr: PExpr<V> = if let Some(cst) = self.try_cst()? {
                self.ws_cmt();
                cst.into()
            } else if let Some(var) = parse_var(self)? {
                self.ws_cmt();
                PExpr::new_var(var)
            } else if self.try_tag("(") {
                self.ws_cmt();
                let op = self.op()?;
                self.ws_cmt();
                stack.push((op, vec![]));
                continue 'go_down_applications;
            } else {
                bail!(self.fail("unexpected token"));
            };

            'go_up_stack: while let Some((op, mut args)) = stack.pop() {
                args.push(expr);

                if self.try_tag(")") {
                    self.ws_cmt();
                    expr = PExpr::new_op(op, args).map_err(|e| e.force_source(self.fail("")))?;
                    continue 'go_up_stack;
                } else {
                    stack.push((op, args));
                    continue 'go_down_applications;
                }
            }

            return Ok(expr);
        }
    }
}

/// SMT2 stateless var and value parser.
#[derive(Debug, Clone, Copy)]
pub struct Smt2Parser;
impl<'a> IdentParser<Var, Typ, &'a str> for Smt2Parser {
    fn parse_ident(self, input: &'a str) -> SmtRes<Var> {
        let mut parser = Parser::new(input);
        match parser.try_var() {
            Ok(Some(var)) => Ok(var),
            Ok(None) | Err(_) => bail!("unexpected variable string `{}`", input),
        }
    }
    fn parse_type(self, input: &'a str) -> SmtRes<Typ> {
        match input {
            "Bool" => Ok(Typ::Bool),
            "Int" => Ok(Typ::Int),
            "Real" => Ok(Typ::Rat),
            _ => bail!("unexpected type string `{}`", input),
        }
    }
}
impl<'a> IdentParser<SVar, Typ, &'a str> for Smt2Parser {
    fn parse_ident(self, input: &'a str) -> SmtRes<SVar> {
        let mut parser = Parser::new(input);
        match parser.try_svar() {
            Ok(Some(svar)) => Ok(svar),
            Ok(None) | Err(_) => bail!("unexpected state variable string `{}`", input),
        }
    }
    fn parse_type(self, input: &'a str) -> SmtRes<Typ> {
        match input {
            "Bool" => Ok(Typ::Bool),
            "Int" => Ok(Typ::Int),
            "Real" => Ok(Typ::Rat),
            _ => bail!("unexpected type string `{}`", input),
        }
    }
}
