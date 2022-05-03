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
            println!("Error:\n{}", e.pretty(()));
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
