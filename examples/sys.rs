fn run() {
    let input = mikino_api::TRANS_DEMO;

    println!("```");
    for line in input.trim().lines() {
        println!("{}", line);
    }
    println!("```");

    println!();
    println!();

    println!("parsing and building transition system...");

    match mikino_api::parse::trans(input) {
        Ok(_) => (),
        Err(e) => {
            for e in e.into_iter() {
                for (idx, line) in e.pretty(()).lines().enumerate() {
                    let pref = if idx == 0 { "- " } else { "  " };
                    println!("{}{}", line, pref);
                }
            }
            std::process::exit(2);
        }
    }

    println!("success");
}

fn main() {
    run()
}

#[test]
fn test_sys() {
    run()
}
