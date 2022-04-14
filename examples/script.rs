fn run() {
    let input = "
set_options!(
    conservative-decls: true,
    produce-models: true,
)

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
    ";

    println!("```");
    for line in input.trim().lines() {
        println!("{}", line);
    }
    println!("```");

    println!();
    println!();

    println!("parsing and building hsmt script...");

    let s = match mikino_api::parse::script(input) {
        Ok(s) => {
            println!();
            println!("got a script:");
            println!("{:#?}", s);
            s
        }
        Err(e) => {
            for e in e.into_iter() {
                for (idx, line) in e.pretty(()).lines().enumerate() {
                    let pref = if idx == 0 { "- " } else { "  " };
                    println!("{}{}", pref, line);
                }
            }
            std::process::exit(2);
        }
    };

    println!();
    println!();

    let _s = match mikino_api::script::build::doit(s) {
        Ok(s) => {
            println!();
            println!("built a script:");
            println!("{:#?}", s);
            s
        }
        Err(e) => {
            mikino_api::prelude!();
            let span = e.span;
            let (prev, row, col, line, next) = span.pretty_of(input);
            let e = Error::parse("", row, col, line, prev, next).extend(e.error.into_iter());
            for e in e.into_iter() {
                for (idx, line) in e.pretty(()).lines().enumerate() {
                    let pref = if idx == 0 { "- " } else { "  " };
                    println!("{}{}", pref, line);
                }
            }
            std::process::exit(2);
        }
    };

    // let script = mikino_api::script::Script::new(script);

    println!("success");
}

fn main() {
    run()
}

#[test]
fn test_sys() {
    run()
}
