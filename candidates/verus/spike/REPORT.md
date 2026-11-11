# Verus spike report

Everything verified at the first or second attempt; see JOURNAL.md.
Files: `spike.rs` (single source), `Cargo.toml`, `.cargo/config.toml`,
`spike.mjs`, `test.mjs`, `spike.wasm` (476 bytes).

## What the theorems state (about `spike.rs`, Rust source, run by Verus as host x86_64)
Verus result: `7 verified, 0 errors` (1.3 s).
- `is_surrogate_impl(cp: u32) -> r` ensures `r == is_surrogate_spec(cp as int)`
  where the spec is `0xD800 <= cp <= 0xDFFF`, for every u32. Plus lemma
  `is_surrogate_examples` (the six LAWS.bend examples), proved by the SMT solver
  with an empty body. The spec and implementation are nearly the same
  expression, so for this tiny function the proof is a weak check.
- `count_non_ascii_core(buf: &[u8]) -> r` (requires `buf.len() <= u32::MAX`)
  ensures `r == count_spec(buf@)`, `count_spec` being a recursive spec fn on
  `Seq<u8>`. Verus also proves absence of panic/overflow/out-of-bounds in the
  loop (arithmetic overflow `n + 1` and indexing are proof obligations).
  Loop invariant: `n == count_spec(buf@.take(i))`, `n <= i`. One
  extensional-equality hint was required.
- Existential lemma `count_exists_unique(s)`: `exists c. count_rel(s,c) &&
  forall d. count_rel(s,d) ==> d == c`, where `count_rel` is
  `s.filter(>=0x80).len() == c`; also proved `count_spec(s) == filter len`
  by induction using a vstd filter lemma. Negative test: changing `>=` to `>`
  in either function made verification fail (as it should).
The theorems are about the exec Rust functions as Verus understands Rust
semantics, not about the wasm. The `extern "C"` exports are NOT verified.

## Trusted / unverified between theorem and running Wasm
No `external_body`, `assume`, `admit`, or `external` was used (grep to confirm).
Unverified or trusted:
1. Verus itself, its Rust-semantics encoding, and Z3 (not foundational).
2. The export shim (plain Rust outside `verus!`, so not verified):
   `is_surrogate_code_point` (`bool as u32`); `count_non_ascii` does
   `unsafe { slice::from_raw_parts(ptr, len) }` and the guard
   `len > u32::MAX => return 0`. The unsafe call's safety contract
   (ptr valid for len bytes, initialised) is trusted, and justified only by
   the JS wrapper writing the bytes there. Verus cannot state it without
   PPtr/PointsTo ghost permissions (not tried).
3. Erasure: the wasm is made by rustc, not by Verus. The `verus!` macro, when
   run by plain rustc, erases ghost code (the verified function bodies are
   identical, loop invariants and proofs dropped). Verus's own erasure and
   the proc-macro erasure are separate implementations; trusted to agree.
4. rustc 1.99.1 / LLVM wasm32 backend, `core` library, wasm-ld, release
   opt-level=s + LTO.
5. Version skew: Verus verified against its bundled prebuilt vstd (release
   0.2026.11.02.8bf68ee); the wasm build used crates.io vstd
   0.0.0-2026-11-01-0251 (same weekly series, one release older). Only
   erased/ghost items come from vstd, so no code of it reaches the wasm, but
   it is an uncontrolled mismatch to pin in a real project.
6. Spec fidelity (hand translation of LAWS.bend), JS wrapper (memory
   placement at `__heap_base`, `memory.grow`, u8 copy), Node/V8.

## Same source? Which target?
- Same source file `spike.rs`, byte for byte, fed to both tools. Verus
  verified it for the HOST target (x86_64-unknown-linux-gnu, usize = 64 bit).
  Verus cannot be run with `--target wasm32-unknown-unknown`: the prebuilt
  `libvstd.rlib` is host-only (error E0461). It would need vstd built for
  wasm32 from Verus source (vargo), not tried. The attempt was one command.
- Consequence: usize width differs (verified with 64-bit usize, run with 32-bit).
  The proof is written so as not to depend on width (`len <= u32::MAX` is a
  precondition, trivially true on wasm32 and checked in the shim for
  others), but Verus did not check this.
- `#![no_std]` works; no allocator, no `alloc`; vstd with
  `default-features = false` compiles for wasm32 (erased mode).
- A `#[panic_handler]` is needed for the wasm build, using
  `core::arch::wasm32::unreachable()`; behind `cfg(target_arch="wasm32")` so the
  host Verus run is unaffected.

## .wasm
476 bytes (`opt-level=s`, LTO, `panic=abort`), no imports, exports `memory`,
`count_non_ascii`, `is_surrogate_code_point`, `__heap_base` (needed by the JS
wrapper, requires `-C link-arg=--export=__heap_base`). Cold build 23 s
(downloads and compiles the macro crates), warm 3 s.

## Inefficiency pressure
Little seen. The loop is a plain byte loop with `u32` counter; spec-driven
style (invariant over `Seq::take`) imposes no data structure. For the real
decoder, risks to watch (not observed): needing `u32`/`usize` casts for
arithmetic, and `Vec`/slice APIs limited to what Verus supports. The
`n <= i` side invariant was needed only for the overflow proof.

## Spec language vs LAWS.bend style
Verus quantifiers and `exists`/`forall` over `Seq<u8>` are direct. The
existence+uniqueness lemma above went through immediately, but it was easy
because `count_rel` was defined through a function (`filter(..).len()`), so
uniqueness was functionality. Not tried: purely inductive relations or
existentials nested over lists (e.g. "there exists a scalar list such that
decode relation holds, and it is unique"), where witnesses and triggers need
manual hints (`choose`, trigger annotations). Judgement: expressible and
readable, a spec reviewer reads standard Rust-flavoured logic; proofs of
inductive uniqueness laws will take hand-written lemmas, and SMT
instability is the risk, not seen at this size. No dependent computation
(`decide`) for byte-case enumeration; `by (bit_vector)` / `by (compute)` exist.
