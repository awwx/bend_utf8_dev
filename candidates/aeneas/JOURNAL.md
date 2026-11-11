# Journal (times are the VM clock, 2026-11-11)

- 10:48 Start. Read survey. Survey said "build from source"; the GitHub releases page has daily nightlies with linux-x86_64
  binaries (including charon) and a prebuilt Lean build. Used those: no OCaml/opam needed.
- 10:49 Downloads done (220 MB, seconds). The release does not ship a ready Lean project: the library sources are in
  `backends/lean` inside the aeneas tarball, and the "lean-build" tarball must be unpacked into `.lake/build` of that
  directory. Figured this out by looking at the lakefile (`buildArchive`), not from docs.
- 10:50 First `lake` call auto-installed Lean v4.36.0-rc2 via elan (the lean-toolchain), in the background. Default toolchain unchanged.
- 10:51 Mistake: `rustup` was not on my PATH (cargo/bin not exported in my shell); my first install attempt silently did
  nothing ("rustup: command not found" in the log, not noticed for 2 min). Re-ran with PATH; 1m48s.
- 10:50-10:55 `lake exe cache get`: clone Mathlib then 9081 files, 5.5 min, 200 KB/s; the slow part. Meanwhile wrote the Rust.
- 10:55 Setup complete (7.5 min).
- Charon failure 1: `error: unwinding panics are not supported without std`. no_std lib compiled by charon in the dev profile
  with panic=unwind. Fix: `[profile.dev] panic = "abort"` in Cargo.toml.
- Charon failure 2 (really an Aeneas one): I had guarded the shim with `#[cfg(not(charon))]`; Charon does NOT set that cfg,
  so the unsafe shim was translated (Aeneas even modelled `ConstRawPtr` and `core::slice::raw::from_raw_parts`!) and the
  `#[panic_handler]` failed with "name already in the names set: panic" and left a `sorry`. Fix: put the shim in `mod shim`
  and pass `--exclude crate::shim` to charon (the excluded code is still compiled by rustc, so the host build needs a
  panic handler too; it lives in the shim module, no cfg).
- Aeneas output: `Result` is now an ITree-based type (constructors `ret`/`vis`/`div`, not `ok`/`fail`/`div`; `ok` is a def). Cost me
  a failed `cases r with | ok | fail`. `cases r with | ret v | vis e k | div` works.
- Lean-side: default `lean` is v4.34 -> "incompatible header" on olean. Use `elan run <toolchain> lean` (build.sh).
- Proofs: (a) 3 attempts (wrong lemma name `UScalar.ge_equiv`, then `decide` can't decide `Result` equality; `simp [fn]` works).
  (b) `loop.spec_decr_nat` + `step*` + omega. Main friction: relating `i3 = i+1` inside `List.drop` (needed `rw [i3_post]` after
  unfolding my invariant def), `List.drop_eq_nil_of_le` argument names, `scalar_tac` closing goals that `step*` had already
  closed (error "no goals"). About 12 build iterations of ~10 s each; first working proof of (a)+(b) about 8 minutes after start,
  early-exit variants about 6 more minutes.
- Early `return`, `break`, `continue` in a single (non-nested) loop: Charon and Aeneas accepted all, no workaround needed.
  Nested-loop cases not tested.
- Wasm build and node test passed first time. Wasm has no allocator; JS grows memory by whole pages to place input.
- 11:01 Done. Spike wall-clock about 6 min of tool time after setup (well under the 40 min box).
