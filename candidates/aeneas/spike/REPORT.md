# Aeneas spike report

Outcome: all of 2a, 2b (including early-exit variants), 2c done. `lean/build.sh` compiles with no `sorry`, no added axioms.

## What the theorems state (all in `lean/Spike/Proofs.lean`, about the Aeneas-generated model `lean/Spike/Funs.lean`)
Specs (`lean/Spike/Spec.lean`, hand-written, independent of Rust and of the model): `IsSurrogate cp := 0xD800 <= cp /\ cp <= 0xDFFF` on `Nat`;
`countNonAscii : List Nat -> Nat` (structural recursion); `firstNonAscii` (index of first byte >= 128, or length).
Spec-only example theorems (the six LAWS.bend examples; count/first examples) are proved by `decide`, no axioms.

- `is_surrogate_code_point_correct (cp : U32) : exists b, is_surrogate_code_point cp = ok b /\ (b = true <-> IsSurrogate cp.val)`. All u32; cannot fail.
- `is_surrogate_code_point_examples`: the six examples hold on the generated function.
- `count_non_ascii_correct (s : Slice U8) (hlen : s.length <= U32.max) : exists r, count_non_ascii s = ok r /\ r.val = countNonAscii (bytesOf s)`
  where `bytesOf s = s.val.map (.val)`. `= ok r` means no panic/overflow/out-of-bounds. The bound is needed in the model (a `u32` counter);
  on wasm32 `usize` is 32 bits so it always holds, but the theorem does not know that (Aeneas assumes usize >= 32 bits, otherwise abstract).
- `first_non_ascii_return_correct`, `first_non_ascii_break_correct` (no bound needed): result = `firstNonAscii (bytesOf s)`, never fails.
- `#print axioms`: every final theorem: `[propext, Classical.choice, Quot.sound]` only (spec examples: none). No Aeneas axioms are used,
  because the std functions touched (`Slice.index_usize`, `Slice.len`, scalar add/compare) are defined, not axiomatised, in this library version.
  (`native_decide`, `bv_decide` not used.)

## Trusted / unverified between theorem and running Wasm
1. Lean kernel + the three standard axioms.
2. The theorem statements and specs (human-reviewed part). Note `bytesOf`/`Slice` is an Aeneas type, so the reviewed spec of a real decoder would be stated through Aeneas's `Slice`/`U8` model, or via a bridge lemma.
3. Charon (rustc MIR -> LLBC) and Aeneas (LLBC -> Lean): unverified implementations (paper-level proofs only).
4. Aeneas Lean standard library models of `core` (Result monad, scalar semantics, slice indexing, `Usize` abstract width): correct only if they match rustc semantics.
5. Charon runs rustc on the host (x86_64, dev profile, panic=abort, no optimisation) while the Wasm is built for wasm32 in release. I confirmed that translating with `--target wasm32-unknown-unknown` gives a byte-identical `Funs.lean` (modulo the module name), so the MIR-level translation agrees; but nothing mechanical checks this in the workflow, it is a manual diff.
6. The unsafe `extern "C"` shim (`mod shim`, `slice::from_raw_parts` on a raw pointer, `as u32` for the bool): excluded from translation with `charon --exclude crate::shim`, so it is unverified. The JS wrapper's ptr/len contract (grow memory, copy, pass) is likewise unverified. (Aeneas can translate the shim, with raw-pointer models, but it did not look useful and the panic handler broke naming.)
7. rustc/LLVM (opt-level s, LTO) and its wasm backend; the Node engine.

Same source? Yes: the single `src/lib.rs` is used by both `charon.sh` and `cargo build --target wasm32-unknown-unknown`; only the `shim` module (and its `#[panic_handler]`) is outside the translation. `Cargo.toml` profiles differ between the two (dev panic=abort vs release panic=abort + LTO + opt-level s) and nothing enforces equivalence. Panic behaviour: in the Wasm a panic loops forever (`panic_handler` is `loop {}`); the theorem says `ok r` so panics are unreachable for inputs satisfying the bound, assuming the shim is called with a valid ptr/len.

## Artifacts
`.wasm`: 468 bytes (release, opt-level s, LTO, `no_std`, no allocator, no imports; exports `memory`, `spike_count_non_ascii`, `spike_is_surrogate_code_point`). `node test.mjs` passes (examples, all code points < 0x110000, edge u32, several buffers including 200 kB).

## Readability of the generated Lean
Good. 139 lines for four small functions; it mirrors the Rust (`if cp >= 55296#u32 then ok (cp <= 57343#u32) else ok false`), loops become a `*_loop.body` function returning `ControlFlow` plus a `loop` wrapper, docstrings give Rust source lines. Types file empty for this crate.

## Proof automation
`step` / `step*` (successor of `progress`) handled `Slice.index_usize` (its `@[step]` lemma discharged the bound from `i < s.len` in context) and the `+ 1` arithmetic with automatic overflow side goals; `scalar_tac` and `omega` closed bounds. `loop.spec_decr_nat` gives a clean invariant+measure interface for `loop`. `simp [fn]` evaluates the generated `if`s on numerals. Friction: the post-condition is `spec m P` (written `m ⦃ r => .. ⦄`), `Result` is now an interaction-tree type, so extracting `exists r, m = ok r` requires `cases r with | ret | vis | div` (no ready lemma found); definitions-as-invariants must be unfolded manually before `rw`; reasoning about `List.drop` indexes needed small helper lemmas (`count_drop`, `first_drop`). Proof size: about 200 lines for these three loops (versus 25 lines of Rust), mostly boilerplate that repeats between loops.

## Control flow
Single `while` with early `return`, and `loop { .. break; .. continue }`: accepted by Charon and Aeneas, translated to the same `ControlFlow` loop body (`done`/`cont`), proofs went through with the same pattern. Not tested: `return`/`break`/`continue` out of nested loops (README says restricted).

## Pushes toward inefficient or awkward implementations
- Indexed `while i < len { bytes[i] }` is what the model likes (`Slice.index_usize` has a clean spec); iterators/`chunks` are supported in principle but less trodden. The Wasm retains bounds checks that the proof shows unreachable (LLVM may or may not remove them; at 468 bytes no cost visible).
- Counters must be explicit machine integers with `+` that Aeneas checks for overflow, forcing bound hypotheses (here `len <= U32.max`) or wider counters.
- Streaming decoder state would be a struct passed by `&mut`; supported by Aeneas (backward functions), not exercised here.
- Spec must be stated over Aeneas's `Slice`/`U8`/`U32` or via a conversion function (`bytesOf`), a small readability cost for the reviewer.
