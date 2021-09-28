//! Parser tests.

use crate::prelude::{parse::*, *};

fn run<T>(input: impl AsRef<str>, action: impl FnOnce(&str) -> Res<T>, expected: Result<&str, &str>)
where
    T: fmt::Display,
{
    let input = input.as_ref();
    println!("input:");
    for line in input.lines() {
        println!("    {}", line);
    }
    let res = action(input)
        .map(|t| t.to_string())
        .map_err(|e| e.to_string());
    match res {
        Ok(t) => assert_eq!(Ok(&t.to_string() as &str), expected),
        Err(e) => assert_eq!(Ok(&e.to_string() as &str), expected),
    }
}

#[test]
fn error_pos() {
    run(
        "// Blah.\nerr_token",
        |input| sys(input).map(|_| "sys"),
        Ok("parse error at 2:1:  | err_token<EOI>, expected \"svars\", run mikino in 'demo' mode for more details about the syntax"),
    );
    run(
        "// Blah.",
        |input| sys(input).map(|_| "sys"),
        Ok("parse error at 1:9:  | // Blah.<EOI>, expected \"svars\", run mikino in 'demo' mode for more details about the syntax"),
    );
}

#[test]
fn span() {
    let input = "here is\nsome\ntext";
    println!("|===| input ({})", input.len());
    for line in input.lines() {
        println!("| {}", line);
    }
    println!("|===|");
    macro_rules! run {
        { $pos:expr => @($row:expr, $col:expr) $prev:expr, $line:expr, $next:expr $(,)? } => {{
            let (in_prev, in_next): (Option<&str>, Option<&str>) = ($prev, $next);
            let span = Span::new($pos, $pos);
            let (prev, row, col, line, next) = span.pretty_of(input);
            println!("{} =>", $pos);
            println!("    {: >15} | {:}", "GOT", "EXPECTED");
            println!("    {: >15} | {:?}", format!("{:?}", prev), in_prev);
            println!("    {: >15} | {:?}", format!("{:?}", row), $row);
            println!("    {: >15} | {:?}", format!("{:?}", col), $col);
            println!("    {: >15} | {:?}", format!("{:?}", line), $line);
            println!("    {: >15} | {:?}", format!("{:?}", next), in_next);
            assert_eq!(prev.as_ref().map(|s| s.as_ref()), in_prev);
            assert_eq!(row, $row);
            assert_eq!(col, $col);
            assert_eq!(line, $line);
            assert_eq!(next.as_ref().map(|s| s.as_ref()), in_next);
        }}
    }

    // Start.
    run!(0 => @(0, 0) None, "here is", Some("some"));
    // Inside first line.
    run!(3 => @(0, 3) None, "here is", Some("some"));
    // First line's last char.
    run!(6 => @(0, 6) None, "here is", Some("some"));
    // First line's newline.
    run!(7 => @(0, 7) None, "here is", Some("some"));

    // Second line.
    run!(8 => @(1, 0) Some("here is"), "some", Some("text"));
    run!(10 => @(1, 2) Some("here is"), "some", Some("text"));
    run!(11 => @(1, 3) Some("here is"), "some", Some("text"));
    run!(12 => @(1, 4) Some("here is"), "some", Some("text"));

    // Last line.
    run!(15 => @(2, 2) Some("some"), "text<EOI>", None);
    run!(16 => @(2, 3) Some("some"), "text<EOI>", None);
    run!(17 => @(2, 4) Some("some"), "text<EOI>", None);

    // EOI.
    run!(input.len() => @(2, 4) Some("some"), "text<EOI>", None);
}

#[test]
fn errors() {
    fn run(input: &str, expected: &[&str]) {
        let mut expected = expected.iter().map(|s| *s);
        println!("input:");
        for line in input.lines() {
            println!(" | {}", line);
        }
        match crate::parse::sys(input) {
            Ok(_) => panic!("got an okay result"),
            Err(e) => {
                for e in e.into_iter() {
                    let expected = expected
                        .next()
                        .expect("got longer error chain than expected");
                    println!("error:");
                    for line in e.pretty(()).lines() {
                        println!("    {}", line);
                    }

                    assert_eq!(&e.pretty(()), expected);
                }
            }
        }

        if let Some(next) = expected.next() {
            println!("expected more errors:");
            println!("{}", next);
            if let Some(n) = expected.fold(None, |acc, _| Some(acc.unwrap_or(0) + 1)) {
                println!("and {} more", n);
            }
        }
    }

    macro_rules! run {
        {
            $input:expr =>
            $($expected:expr),+ $(,)?
        } => {run(
            $input,
            &[$($expected),+]
        )};
    }

    run!(
        "" =>
        "\
parse error at 1:1
  |
1 | <EOI>
  | ^~~~ here\
        ",
        r#"expected "svars""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars" =>
        "\
parse error at 1:6
  |
1 | svars<EOI>
  |      ^~~~ here\
        ",
        r#"expected "{""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars {}" =>
        "\
parse error at 1:8
  |
1 | svars {}<EOI>
  |        ^~~~ here\
        ",
        r#"expected list of "<ident>, <ident>, ... : <type>""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v }" =>
        "\
parse error at 1:9
  |
1 | svars { v }<EOI>
  |         ^~~~ here\
        ",
        r#"expected list of "<ident>, <ident>, ... : <type>""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }" =>
        "\
parse error at 1:18
  |
1 | svars { v : int }<EOI>
  |                  ^~~~ here\
        ",
        r#"expected "init""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit" =>
        "\
parse error at 2:5
  | svars { v : int }
2 | init<EOI>
  |     ^~~~ here\
        ",
        r#"expected "{""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { " =>
        "\
parse error at 2:8
  | svars { v : int }
2 | init { <EOI>
  |        ^~~~ here\
        ",
        r#"expected comma-separated list of stateless expressions"#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true" =>
        "\
parse error at 2:12
  | svars { v : int }
2 | init { true<EOI>
  |            ^~~~ here\
        ",
        r#"expected "}""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true }" =>
        "\
parse error at 2:14
  | svars { v : int }
2 | init { true }<EOI>
  |              ^~~~ here\
        ",
        r#"expected "trans""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true }\ntrans {" =>
        "\
parse error at 3:8
  | init { true }
3 | trans {<EOI>
  |        ^~~~ here\
        ",
        r#"expected comma-separated list of stateful expressions"#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true }\ntrans { true" =>
        "\
parse error at 3:13
  | init { true }
3 | trans { true<EOI>
  |             ^~~~ here\
        ",
        r#"expected "}""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true }\ntrans { true }" =>
        "\
parse error at 3:15
  | init { true }
3 | trans { true }<EOI>
  |               ^~~~ here\
        ",
        r#"expected "candidates""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true }\ntrans { true }\ncandidates" =>
        "\
parse error at 4:11
  | trans { true }
4 | candidates<EOI>
  |           ^~~~ here\
        ",
        r#"expected "{""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true }\ntrans { true }\ncandidates {" =>
        "\
parse error at 4:13
  | trans { true }
4 | candidates {<EOI>
  |             ^~~~ here\
        ",
        r#"expected list of "<name> : <expr>" where <name> is a double-quoted string"#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true }\ntrans { true }\ncandidates { \"prop\"" =>
        "\
parse error at 4:14
  | trans { true }
4 | candidates { \"prop\"<EOI>
  |              ^~~~ here\
        ",
        r#"expected list of "<name> : <expr>" where <name> is a double-quoted string"#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true }\ntrans { true }\ncandidates { \"prop\" :" =>
        "\
parse error at 4:14
  | trans { true }
4 | candidates { \"prop\" :<EOI>
  |              ^~~~ here\
        ",
        r#"expected list of "<name> : <expr>" where <name> is a double-quoted string"#,
        "run mikino in 'demo' mode for more details about the syntax",
    );

    run!(
        "svars { v : int }\ninit { true }\ntrans { true }\ncandidates { \"prop\" : true" =>
        "\
parse error at 4:27
  | trans { true }
4 | candidates { \"prop\" : true<EOI>
  |                           ^~~~ here\
        ",
        r#"expected "}""#,
        "run mikino in 'demo' mode for more details about the syntax",
    );
}
