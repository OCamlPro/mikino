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
        Ok("error at 2:1: expected \"state\""),
    );
    run(
        "// Blah.",
        |input| sys(input).map(|_| "sys"),
        Ok("error at 1:9: expected \"state\""),
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
    run!(15 => @(2, 2) Some("some"), "text", None);
    run!(16 => @(2, 3) Some("some"), "text", None);
    run!(17 => @(2, 4) Some("some"), "text", None);

    // EOI.
    run!(input.len() => @(2, 4) Some("some"), "text", None);
}
