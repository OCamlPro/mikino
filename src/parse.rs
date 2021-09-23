//! Transition system parser.

crate::prelude!();

use expr::{Cst, Expr, Op, PExpr, SExpr, SVar, Typ, Var};
use rsmt2::parse::IdentParser;
use trans::{Decls, Sys};

mod ast;
pub mod kw;

pub use ast::*;

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
    pub grammar rules() for str {
        /// Whitespace.
        pub rule whitespace() = quiet! {
            [ ' ' | '\n' | '\t' ]
        }
        /// Comment.
        ///
        /// ```rust
        /// # use mikino_api::{trans::Decls, parse::rules::comment};
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
            [^ '/' | '!' | '\n' ]*
            // Newline or EOI.
            ("\n" / ![_])
        }
        / expected!("non-documentation comment")

        /// Whitespace or comment.
        rule _() = quiet! { ( whitespace() / comment() )* }

        /// Ident parsing.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::{trans::Decls, parse::rules::ident};
        ///
        /// // Regular idents are okay.
        /// assert_eq!(*ident("v_1").unwrap(), "v_1");
        /// assert_eq!(*ident("my_var_7").unwrap(), "my_var_7");
        ///
        /// // Cannot start with a digit.
        /// assert_eq!(
        ///     ident("0_illegal").unwrap_err().to_string(),
        ///     "error at 1:1: expected quoted or unquoted identifier",
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
        / expected!("quoted or unquoted identifier")


        /// Parses boolean constants.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::{trans::Decls, parse::rules::bool};
        ///
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
        /// # use mikino_api::{trans::Decls, parse::rules::number};
        ///
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
        ///
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
        /// # use mikino_api::{trans::Decls, parse::rules::uint, prelude::Int};
        ///
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


        /// Parses an unsigned [`Int`], cannot be followed by a `.`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use mikino_api::{trans::Decls, parse::rules::decimal, prelude::{Int, Rat}};
        ///
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

        pub rule cst() -> Spn<Cst>
        =
        rat:decimal() {
            rat.map(Cst::R)
        }
        / int:uint() {
            int.map(Cst::I)
        }
        / b:bool() {
            b.map(Cst::B)
        }

        /// Parses variables.
        pub rule hsmt_var() -> Ast<'input>
        = var:ident() prime:(
            ps:position!() "'" pe:position!() {
                Span::from((ps, pe))
            }
        )? {
            Ast::svar(var, prime)
        }

        /// Parses an if-then-else.
        ///
        /// No parens needed.
        rule hsmt_ite() -> Ast<'input>
        = quiet! {
            s:position!() "if" e:position!()
            _ cnd:hsmt()
            _ "then"
            _ thn:hsmt()
            _ "else"
            _ els:hsmt() {
                Ast::app(Spn::new(Op::Ite, (s,e)), vec![cnd, thn, els])
            }
        }
        / expected!("if-then-else")

        /// Parses polymorphic expressions.
        /// Parses stateful expressions.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use mikino_api::parse::rules::hsmt;
        /// let ast = hsmt(
        ///     "if a ∧ n ≥ 10 then n' = n - 1 else if false then n' > n else false"
        /// ).unwrap();
        /// assert_eq!(
        ///     ast.to_string(),
        ///     "(\
        ///         if (a ⋀ (n ≥ 10)) \
        ///         then (n' = (n - 1)) \
        ///         else (if false then (n' > n) else false)\
        ///     )",
        /// )
        /// ```
        ///
        /// ```rust
        /// use mikino_api::parse::rules::hsmt;
        /// let ast = hsmt(
        ///     "a ∧ x ≥ 7 - m ∨ if 7 = n + m then b_1 ∨ b_2 else c"
        /// ).unwrap();
        /// assert_eq!(
        ///     ast.to_string(),
        ///     "((a ⋀ (x ≥ (7 - m))) ⋁ (if (7 = (n + m)) then (b_1 ⋁ b_2) else c))",
        /// )
        /// ```
        pub rule hsmt() -> Ast<'input>
        = ast:precedence! {
            // Implication, right associative.
            lft:@ _ s:position!() (
                "=>" / "⇒" / "→" / "⊃"
             ) e:position!() _ rgt:(@) {
                Ast::binapp(Spn::new(Op::Implies, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() (
                "∨" / "⋁" / "||"
             ) e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Or, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() (
                "∧" / "⋀" / "&&"
            ) e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::And, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() "<" e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Lt, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() ("<=" / "≤") e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Le, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() (">=" / "≥") e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Ge, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() ">" e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Gt, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() "=" e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Eq, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() "+" e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Add, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() "-" e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Sub, (s, e)), lft, rgt)
            }
            --
            lft:(@) _ s:position!() "*" e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Mul, (s, e)), lft, rgt)
            }
            lft:(@) _ s:position!() "/" e:position!() _ rgt:@ {
                Ast::binapp(Spn::new(Op::Div, (s, e)), lft, rgt)
            }
            --
            s:position!() ("¬" / "!") e:position!() _ arg:@ {
                Ast::unapp(Spn::new(Op::Not, (s, e)), arg)
            }
            s:position!() "-" e:position!() _ arg:@ {
                Ast::unapp(Spn::new(Op::Sub, (s, e)), arg)
            }
            --
            ite:hsmt_ite() {
                ite
            }
            var:hsmt_var() {
                var
            }
            cst:cst() {
                Ast::cst(cst)
            }
            "(" _ e:hsmt() _ ")" {
                let mut e = e;
                e.close();
                e
            }
        }

        /// Parses a type.
        pub rule hsmt_typ() -> expr::Typ
        = "int" { expr::Typ::Int }
        / "rat" { expr::Typ::Rat }
        / "bool" { expr::Typ::Bool }

        /// Parses some declarations.
        pub rule hsmt_decls() -> PRes<trans::Decls>
        = "("
            state:(
                _ svar:ident() svars:( _ "," _ id:ident() { id })*
                _ ":" _ svars_typ:hsmt_typ() {
                    (svar, svars, svars_typ)
                }
            )*
        _ ")" {
            let mut decls = trans::Decls::new();
            for (svar, svars, typ) in state {
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
        pub rule candidates() -> Vec<(Spn<&'input str>, Ast<'input>)>
        = "(" candidates:(
            _ s:position!() name:$(
                "\"" ("\\\"" / [^'"'])* "\""
            ) e:position!() _ ":" _
            expr:hsmt() {
                (Spn::new(name, (s, e)), expr)
            }
        )+ _ ")" {
            candidates
        }

        /// Parses a full instance.
        pub rule hsmt_instance() -> PRes<trans::Sys>
        =
        _ "state" _ decls:hsmt_decls()
        _ "init" _ "(" _ init:hsmt() _  ")"
        _ "trans" _ "(" _ trans:hsmt() _ ")"
        _ "candidates" _ candidates:candidates()
        _ {
            let decls = decls?;
            let init = init.to_expr(&decls)?;
            let trans = trans.to_sexpr(&decls)?;

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
    }
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
    pub fn fail_at(&self, pos: usize, msg: impl std::fmt::Display) -> Error {
        let (line, row, col) = match self.pretty_pos(pos) {
            Ok(res) => res,
            Err(e) => {
                return e
                    .chain_err(|| format!("while retrieving pretty position @{}: `{}`", pos, msg))
            }
        };
        ErrorKind::ParseErr(row, col, line, msg.to_string()).into()
    }

    /// Fails at the current position.
    pub fn fail(&self, msg: impl std::fmt::Display) -> Error {
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
            .ok_or_else(|| self.fail("expected an identifier"))
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
                    expr = PExpr::new_op(op, args)
                        .map_err(|e| Error::from(self.fail(e.to_string())))?;
                    continue 'go_up_stack;
                } else {
                    stack.push((op, args));
                    continue 'go_down_applications;
                }
            }

            return Ok(expr);
        }
    }

    /// Parses some declarations.
    pub fn decls(&mut self) -> Res<()> {
        self.tag("vars")
            .chain_err(|| "starting declaration block")?;
        self.ws_cmt();
        self.tag(":").chain_err(|| "before declaration block")?;
        self.ws_cmt();
        self.tag("(").chain_err(|| "starting declaration block")?;
        self.ws_cmt();

        #[allow(unused_labels)]
        'parse_decls: while !self.try_tag(")") {
            let mut ids = vec![(
                self.cursor,
                self.id()
                    .chain_err(|| "or `)` closing variable declarations")?,
            )];
            self.ws_cmt();
            while self.try_tag(",") {
                self.ws_cmt();
                ids.push((self.cursor, self.id().chain_err(|| "after `,`")?));
                self.ws_cmt();
            }
            self.tag(":")
                .chain_err(|| "between identifier(s) and type")?;
            self.ws_cmt();
            let typ = self.typ()?;
            for (start, id) in ids {
                let prev = self.decls.register(id, typ);
                if prev.is_some() {
                    bail!(self.fail_at(start, format!("trying to re-define variable `{}`", id)))
                }
            }
            self.ws_cmt();
        }

        Ok(())
    }

    /// Parses the initial state predicate.
    pub fn init(&mut self) -> Res<Expr> {
        self.tag("init").chain_err(|| "starting init predicate")?;
        self.ws_cmt();
        self.tag(":").chain_err(|| "starting init predicate")?;
        self.ws_cmt();
        self.expr()
    }

    /// Parses the initial state predicate.
    pub fn trans(&mut self) -> Res<SExpr> {
        self.tag("trans")
            .chain_err(|| "starting transition predicate")?;
        self.ws_cmt();
        self.tag(":")
            .chain_err(|| "starting transition predicate")?;
        self.ws_cmt();
        self.sexpr()
    }

    /// Parses the proof obligations of the system.
    pub fn po_s(&mut self) -> Res<Map<String, Expr>> {
        self.tag("po_s")
            .chain_err(|| "starting the list of proof obligations")?;
        self.ws_cmt();
        self.tag(":").chain_err(|| "before proof obligation list")?;
        self.ws_cmt();
        self.tag("(")
            .chain_err(|| "opening proof obligation list")?;
        self.ws_cmt();
        let mut map = Map::new();
        let mut po_start;

        while {
            po_start = self.cursor;
            self.try_tag("\"")
        } {
            let po_name = self.parse_until(|c| c == '"', false).trim();
            self.tag("\"")
                .chain_err(|| "closing proof obligation name")?;
            self.ws_cmt();
            self.tag(":")
                .chain_err(|| "between proof obligation name and its definition")?;
            self.ws_cmt();
            let def = self.expr().chain_err(|| {
                format!(
                    "while parsing definition for proof obligation `{}`",
                    po_name
                )
            })?;
            let prev = map.insert(po_name.into(), def);
            if prev.is_some() {
                bail!(self.fail_at(
                    po_start,
                    format!("illegal re-definition of proof obligation `{}`", po_name),
                ))
            }
            self.ws_cmt();
        }

        self.tag(")")
            .chain_err(|| "closing proof obligation list")?;

        Ok(map)
    }

    /// Parses a full system.
    pub fn sys(mut self) -> Res<Sys> {
        self.ws_cmt();
        self.decls()?;
        self.ws_cmt();
        let init = self.init()?;
        self.ws_cmt();
        let trans = self.trans()?;
        self.ws_cmt();
        let po_s = self.po_s()?;
        self.ws_cmt();
        if !self.is_at_eoi() {
            bail!(self.fail("expected end of file"))
        } else {
            Ok(Sys::new(self.decls, init, trans, po_s))
        }
    }

    pub fn new_sys(self) -> Res<Sys> {
        match rules::hsmt_instance(self.txt) {
            Ok(res) => match res {
                Ok(sys) => Ok(sys),
                Err(e) => {
                    let span = e.span;
                    let (line, row, col) = self
                        .pretty_pos(span.start)
                        .chain_err(|| "internal parse error")?;
                    let err =
                        Error::from(ErrorKind::ParseErr(row, col, line, "parse error".into()));
                    return Err(err.chain_err(|| e.error));
                }
            },
            Err(e) => {
                let (line, row, col) = self
                    .pretty_pos(e.location.offset)
                    .chain_err(|| "internal parse error")?;
                let err = Error::from(ErrorKind::ParseErr(row, col, line, "parse error".into()));
                return Err(err.chain_err(|| e.to_string()));
            }
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
