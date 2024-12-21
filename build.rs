use std::{env, fs, process::Command, str};

struct Check<'a> {
    crate_type: &'a str,
    emit: Option<&'a str>,
}

impl<'a> Check<'a> {
    fn lib() -> Self {
        Self {
            crate_type: "lib",
            emit: Some("llvm-ir"),
        }
    }

    fn bin() -> Self {
        Self {
            crate_type: "bin",
            emit: None,
        }
    }

    fn cfg_from_raw(&self, cfg: &str, src: &str) {
        let out_dir = env::var("OUT_DIR").unwrap();
        let filename = format!("{out_dir}/test.rs");
        fs::write(&filename, src.as_bytes()).unwrap();

        let rustc = env::var("RUSTC").unwrap();
        let mut cmd = Command::new(rustc);
        cmd.arg("--crate-type").arg(self.crate_type);
        if let Some(emit) = self.emit {
            cmd.arg("--emit").arg(emit);
        }
        cmd.arg("--out-dir").arg(&out_dir);
        cmd.arg(&filename);

        println!("cargo:rustc-check-cfg=cfg({cfg})");
        if let Ok(output) = cmd.output() {
            if output.status.success() {
                println!("cargo:rustc-cfg={cfg}");
            } else {
                eprintln!("{}", str::from_utf8(&output.stderr).unwrap());
            }
        }
    }

    fn cfg_from_c_function(&self, cfg: &str, func: &str) {
        let src = format!(
            r#"
                extern "C" {{
                    fn {func}();
                }}
                fn main() {{
                    unsafe {{ {func}() }};
                }}
            "#
        );
        Check::bin().cfg_from_raw(cfg, &src);
    }
}

fn main() {
    Check::lib().cfg_from_raw("has_doc_auto_cfg", "#![feature(doc_auto_cfg)]");
    Check::bin().cfg_from_c_function("has_strcasecmp", "strcasecmp");
}
