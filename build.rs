fn cfg_from_raw(cfg: &str, src: &str) {
    let ac = autocfg::new();
    println!("cargo:rustc-check-cfg=cfg({cfg})");
    if ac.probe_raw(src).is_ok() {
        println!("cargo:rustc-cfg={cfg}");
    }
}

fn main() {
    cfg_from_raw("has_doc_auto_cfg", "#![feature(doc_auto_cfg)]");
}
