mikino_api::prelude!();

fn run() -> Res<()> {
    let input = "
vars!(
    cnt0   cnt1   : int,
    reset0 reset1 : bool,
)

assert!(
    cnt1 = if reset1 { 0 } else { cnt0 + 1 }
)

let is_sat = check_sat!();

if is_sat {
    echo!(\"it's sat\")
    vars!(
        cnt2: int,
        reset2: bool,
    )
    let sat_too = check_sat!();
    if sat_too {
        echo!(\"stuff\")
    } else {}
} else {
    echo!(\"so unsat :(\")
    panic!(\"timeout or unknown result\")
} otherwise {
    vars!(
        cnt2: int,
        reset2: bool,
    )
}

assert!(
    cnt2 = if reset2 { 0 } else { cnt1 + 1}
)

if check_sat!() {
    echo!(\"does not compile\")
}

get_model!()
    ";

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
