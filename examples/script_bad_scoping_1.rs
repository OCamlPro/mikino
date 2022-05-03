mikino_api::prelude!();

fn run() -> Res<()> {
    let input = include_str!("../rsc/script_bad_scoping_1.rs");

    println!("```");
    for line in input.lines() {
        println!("{}", line);
    }
    println!("```");

    println!();
    println!();

    println!("parsing and building hsmt script...");

    let script = mikino_api::parse::script(input)?;

    println!();
    println!();

    let script = mikino_api::script::build::doit(script).map_err(|e| {
        let span = e.span;
        let (prev, row, col, line, next) = span.pretty_of(input);
        Error::parse("", row, col, line, prev, next).extend(e.error.into_iter())
    })?;

    let mut script = {
        let conf = mikino_api::rsmt2::SmtConf::default_z3();
        mikino_api::script::Script::new(conf, None, &script, input)?
    };

    'step: loop {
        use mikino_api::script::Step;
        match script.step()? {
            Step::Done(res) => {
                println!("{}", res.pretty(input, (), true));
                break 'step;
            }
            step => {
                if let Some(pretty) = step.pretty(input, (), true) {
                    println!("{}", pretty)
                }
            }
        }
    }

    Ok(())
}

const EXPECTED: &str = "
- parse error at 52:10
     |
  52 | assert { next_next_var = next_var }
     |          ^~~~ here
- unknown variable `next_next_var`
";
fn expected() -> &'static str {
    EXPECTED.trim()
}

fn fail(blah: &str) {
    println!("{}expected this error:", blah);
    println!();
    println!("```");
    println!("{}", expected());
    println!("```");
    panic!("unexpected result")
}

fn main() {
    match run() {
        Ok(()) => fail("script completed successfully, but "),
        Err(e) => {
            let pretty = e.pretty(());
            let pretty = pretty.trim();
            let debug = false;
            if !debug {
                println!("Error:\n{}", pretty);
            } else {
                println!("Error:");
                for line in pretty.lines() {
                    println!("  `{}`", line)
                }
                println!("Expected:");
                for line in expected().lines() {
                    println!("  `{}`", line)
                }
            }
            println!();
            if pretty == expected() {
                println!("got the expected error, success")
            } else {
                fail("error mismatch, ")
            }
        }
    }
}

#[test]
fn test_sys() {
    main()
}
