fn run() {
    let input = "
vars {
    cnt0   cnt1   : int,
    reset0 reset1 : bool,
}

assert!(
    cnt1 = if reset1 { 0 } else { cnt0 + 1 }
)

let is_sat = check_sat!();

if is_sat {
    echo!(\"it's sat\")
} else {
    echo!(\"so unsat :(\")
} otherwise {
    echo!(\"timeout or unknown result\")
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

    println!("success");
}

fn main() {
    run()
}

#[test]
fn test_sys() {
    run()
}
