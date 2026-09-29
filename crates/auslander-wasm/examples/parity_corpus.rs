//! Writes one portable value per kind and status into a directory.
//!
//! `web/parity.mjs` verifies these files natively and in WebAssembly.
//! Usage: `cargo run -p auslander-wasm --example parity_corpus -- DIR`.

#[path = "../tests/fixtures/mod.rs"]
mod fixtures;

fn main() {
    let directory = std::env::args().nth(1).expect("usage: parity_corpus DIR");
    std::fs::create_dir_all(&directory).expect("create the corpus directory");
    for (name, text) in fixtures::corpus() {
        let path = std::path::Path::new(&directory).join(name);
        std::fs::write(&path, text).expect("write one corpus file");
        println!("{}", path.display());
    }
}
