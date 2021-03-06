mikino_api::prelude!();

fn run() -> Res<()> {
    let input = mikino_api::SCRIPT_DEMO;

    println!("```");
    for line in input.trim().lines() {
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
        mikino_api::prelude!();
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

fn main() {
    match run() {
        Ok(()) => (),
        Err(e) => {
            println!("Error:\n{}", e.pretty(()));
            std::process::exit(2);
        }
    }
}

#[test]
fn test_sys() {
    main()
}
