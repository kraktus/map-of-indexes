use std::env;
use std::fs::File;
use std::io;
use std::io::Write;
use std::path::Path;

fn main() -> io::Result<()> {
    let out_dir = env::var("OUT_DIR").expect("got OUT_DIR");

    let lib_path = Path::new(&out_dir).join("lib.rs");
    let mut f = File::create(&lib_path).expect("created lib.rs");
    generate_key_value_impl(&mut f)
}

fn generate_key_value_impl_from<W: Write>(f: &mut W, a: &str, b: &str) -> io::Result<()> {
    write!(
        f,
        "impl KeyValue for ({a},{b}) {{
	type K = {a};
	type V = {b};
	fn key(&self) -> &Self::K {{
		&self.0
	}}

    fn value(&self) -> &Self::V {{
    	&self.1
    }} 
}}
"
    )
}

fn generate_key_value_impl<W: Write>(f: &mut W) -> io::Result<()> {
    let mut int: Vec<String> = Vec::new();
    for sign in ["u", "i"] {
        for size in ["8", "16", "32", "64", "128", "size"] {
            int.push(sign.to_string() + size)
        }
    }
    for i in 0..int.len() {
        generate_key_value_impl_from(f, &int[i], &int[i])?;
        for j in i + 1..int.len() {
            generate_key_value_impl_from(f, &int[i], &int[j])?;
            generate_key_value_impl_from(f, &int[j], &int[i])?;
        }
    }
    Ok(())
}
