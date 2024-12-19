use std::{env, fs, path::PathBuf};

fn cfg_from_raw(cfg: &str, src: &str) {
    let ac = autocfg::new();
    println!("cargo:rustc-check-cfg=cfg({cfg})");
    if ac.probe_raw(src).is_ok() {
        println!("cargo:rustc-cfg={cfg}");
    }
}

fn cfg_from_raw_c(cfg: &str, src: &str) {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let test = out_dir.join("test.c");
    fs::write(&test, src.as_bytes()).unwrap();
    let has = cc::Build::new()
        .include("#include <string.h>")
        .file(test)
        .try_compile("test_output")
        .is_ok();
    println!("cargo:rustc-check-cfg=cfg({cfg})");
    if has {
        println!("cargo:rustc-cfg={cfg}");
    }
}

fn main() {
    cfg_from_raw("has_doc_auto_cfg", "#![feature(doc_auto_cfg)]");

    cfg_from_raw_c(
        "has_strcasecmp",
        r#"
        #include <string.h>
        int main(int argc, char **argv) { return strcasecmp(argv[1], argv[2]) | argc; }
    "#,
    );
}
