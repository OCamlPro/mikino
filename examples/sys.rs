#![feature(parser, demo)]

fn run() {
    let input = mikino_api::DEMO;

    for line in input.lines() {
        println!("{}", line);
    }

    println!();
    println!();

    println!("parsing and building transition system...");

    let _sys = mikino_api::parse::sys(input).unwrap();

    println!("success");
}

fn main() {
    run()
}

#[test]
fn test_sys() {
    run()
}
