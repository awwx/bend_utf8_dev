# Journal (times +07, 2026-11-11)

- 10:47:45 Start. Read survey section and LAWS.bend 105-135.
- 10:48 Release list via GitHub API; picked the weekly 0.2026.11.02 (not the
  rolling prerelease). Downloaded zip (35 MB), no `unzip` installed -> used
  python zipfile. Zip extraction drops exec bits: `./verus` "Permission
  denied" until chmod +x (confusing, message gives no hint).
- 10:48 `./verus --version` says rustup missing and prints the install
  command. rustup did not exist yet (other agent was not done); installed it
  with `--default-toolchain none`. Then verus said toolchain 1.99.1 missing;
  `rustup toolchain install 1.99.1 --profile minimal -t wasm32-unknown-unknown`
  took ~40 s. Side effect: rustup set 1.99.1 as default since none existed.
- 10:49:05 Setup complete (~1m20s).
- 10:49:21 First spike.rs attempt (written in one go). Verus first run: only
  an error in my panic_handler (core::arch::wasm32 does not exist on host).
  Fixed with cfg(target_arch="wasm32"). Then `7 verified, 0 errors` (1.3 s),
  including the filter-length lemma and existential lemma. No SMT fiddling
  was required, which surprised me. One assert for seq extensional equality
  in the loop was written up front from habit; not verified if removable.
- 10:49:40 Dead end: `verus --target wasm32-unknown-unknown` fails, E0461,
  prebuilt libvstd.rlib is host-only. Did not pursue building vstd for wasm.
- 10:49:50 Route used instead: cargo project depending on crates.io `vstd`
  (default-features=false), plain rustc compiles the erased source. It worked
  first time in 23 s. Needed to pin the exact pre-release version string
  (`=0.0.0-2026-11-01-0251`); crates.io had no release matching the Verus
  zip's date exactly.
- 10:50 JS test failed: `__heap_base` not exported by wasm-ld by default.
  Added `.cargo/config.toml` link-arg `--export=__heap_base` (476 B).
  Tests pass (10:50:28).
- 10:50:37 Negative test (mutated both comparisons): Verus rejects with
  postcondition and invariant errors. Wrote docs. Total spike time under
  4 minutes after setup; no time-box pressure. Not attempted: PPtr-based
  verification of the raw boundary, a truly inductive relational lemma,
  building vstd for wasm32, `cargo verus`.
