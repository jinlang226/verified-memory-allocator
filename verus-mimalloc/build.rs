// rust-analyzer only. `verus!` erases proof/spec items unless this cfg is set,
// which would hide the ghost half of the call graph. Verification itself runs
// through `make verify` and never sees this file.
fn main() {
    println!("cargo::rustc-cfg=verus_keep_ghost");
    println!("cargo::rustc-check-cfg=cfg(verus_keep_ghost)");
}
