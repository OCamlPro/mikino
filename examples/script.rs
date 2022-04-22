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
                println!("{}", res.pretty(input, ()));
                break 'step;
            }
            step => {
                if let Some(pretty) = step.pretty(input, ()) {
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
            for e in e.into_iter() {
                for (idx, line) in e.pretty(()).lines().enumerate() {
                    let pref = if idx == 0 { "- " } else { "  " };
                    println!("{}{}", pref, line);
                }
            }
            std::process::exit(2);
        }
    }
}

#[test]
fn test_sys() {
    main()
}
