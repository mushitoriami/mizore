use std::env;
use std::fs::File;
use std::io::Read;
use std::process;

fn main() {
    let args = env::args().collect::<Vec<String>>();
    if args.len() != 2 {
        eprintln!("Usage: mizore <filename>");
        process::exit(1);
    }
    let Ok(mut file) = File::open(&args[1]) else {
        eprintln!("Cannot open file: {}", &args[1]);
        process::exit(1);
    };
    let mut contents = String::new();
    let Ok(_) = file.read_to_string(&mut contents) else {
        eprintln!("Cannot read file: {}", &args[1]);
        process::exit(1);
    };
    let Some(stmts) = mizore::source_to_stmts(&contents) else {
        eprintln!("Cannot parse source file: {}", &args[1]);
        process::exit(1);
    };
    for range in mizore::verify_module(&stmts, 5) {
        eprintln!("Failed to verify the assertion:\n{}\n", &contents[range]);
    }
}
