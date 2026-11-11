# Source-level candidates (proof about a source program compiled to Wasm)

Survey date: 2026-11-11. Read-only web research; nothing was installed or built, so every
install time / RAM figure is an inference. Tags: **[V: url]** = verified from that source
(fetched or returned by search today); **[I]** = my inference or background knowledge.
Several sources were summarised by a fetch tool, not read verbatim; treat details as
"as reported by the fetch" and re-check before committing.

Common JS boundary pattern for all Rust/C-like candidates [I]: the module exports
`alloc`/fixed static buffers, JS copies the `Uint8Array` into linear memory, calls
`decode(state_ptr, in_ptr, in_len, out_ptr, out_cap) -> counts`, state lives in a
`#[repr(C)]` struct in linear memory (or in a few i32 globals/returns), and text comes out as
UTF-16 code units or UTF-8 bytes read back from linear memory (`TextDecoder` or `String.fromCharCode`).
Output of U+FFFD-replaced UTF-8 is at most 3x input bytes for ill-formed bytes (each lone byte gives a 3-byte U+FFFD), so a caller-sized output buffer is easy. No candidate forces inefficiency here;
the cost lies in the proofs, not the runtime.

---------------------------------------------------------------------------------------------

## 1. Verus (Rust + SMT)

**Links / dates**
- Repo https://github.com/verus-lang/verus ; releases https://github.com/verus-lang/verus/releases
- Latest weekly release `release/0.2026.11.02.8bf68ee` (2026-11-02); rolling prerelease 2026-11-05; weekly cadence since Oct. [V: https://api.github.com/repos/verus-lang/verus/releases]
- Repo toolchain file pins Rust **1.99.1** [V: https://raw.githubusercontent.com/verus-lang/verus/main/rust-toolchain.toml]
- vstd dependency versions dated 2026-11-08 [V: https://raw.githubusercontent.com/verus-lang/verus/main/source/vstd/Cargo.toml]

**Install**
- Prebuilt zips for x86-linux, arm64-linux, macos, win; the x86-linux zip is ~36 MB [V: releases API above]. INSTALL.md: Ubuntu 24.04 x86_64 supported; run `./verus`, which tells you which rustup toolchain to install and the command [V: https://raw.githubusercontent.com/verus-lang/verus/main/INSTALL.md]. Z3 is not mentioned on that page; the release zip historically bundles it [I].
- Also `cargo verus` for multi-crate projects [V: https://verus-lang.github.io/verus/guide/cargo_verus.html].
- Estimate [I]: 5-10 min (download zip, rustup installs 1.99.1 + wasm32 target), <2 GB RAM for small proofs; Z3 is single threaded; verification of a few hundred lines typically seconds to a minute.

**Wasm / no_std**
- No Verus documentation about wasm or no_std found; the guide's cargo-verus page says nothing about targets [V: guide page above; search found nothing]. Only one open wasm-related issue (about an in-browser explorer, not about targets) [V: https://github.com/verus-lang/verus/issues?q=wasm].
- BUT a close precedent exists: `smoothutf8` 0.2.3 (2026-06-29) is a `#![no_std]`, zero-dependency Rust UTF-8 *validator* with Verus proof (84 verified), and its CI builds `wasm32-unknown-unknown` [V: https://docs.rs/crate/smoothutf8/latest ; https://raw.githubusercontent.com/iainmcgin/smooth-utf8/main/README.md ; repo https://github.com/iainmcgin/smooth-utf8, pushed 2026-09-28]. The README does not say the Verus proof is run for the wasm32 build; Verus verifies the host-independent erased-to-normal-Rust program, and the wasm build is plain rustc of the same source [I].
- Verus also has a `std`/`alloc` feature split in vstd (`default=["std"]`, `alloc`) so no_std use is designed in [V: vstd Cargo.toml above]; I could not confirm that vstd itself is `#![no_std]` with default features off [unverified].
- Allocator-free is natural: decoder works on `&[u8]`/`&mut [u8]` slices and a `Copy` state struct [I]. Verus supports slices, `u8` arithmetic, loops with invariants, early return, `Vec` [I, standard Verus features].

**Raw memory / extern "C" boundary**
- Exported `#[no_mangle] pub extern "C" fn` taking `*const u8, usize` needs `unsafe { core::slice::from_raw_parts }`. Verus does not verify raw-pointer derefs on slices without ghost permissions (`PPtr`/`PointsTo`, guide chapter "Pointers") [V: https://raw.githubusercontent.com/verus-lang/verus/main/source/docs/guide/src/SUMMARY.md lists it; content not read]. smoothutf8 handles this with five `external_body` leaf loads and states "the slice-to-pointer bridge" is outside the proof [V: smoothutf8 docs.rs page]. For us: the verified core is `fn decode(state: &mut State, input: &[u8], out: &mut [u16/u8]) -> (usize,usize)`, with a ~10-line unverified `extern "C"` shim around it [I].

**Spec language fit**
- Verus ghost code has `Seq<u8>`, `forall`/`exists`, `choose`, `spec fn`, `proof fn`, recursion, ghost state [V: guide TOC: exists and choose, Quantifiers, Proofs about forall and exists]. Relational specs ("exists a scalar list such that ... and decode relation holds") are expressible as `spec fn rel(bytes: Seq<u8>, out: Seq<char/u32>) -> bool`; existence/uniqueness laws as `proof fn` lemmas with `ensures exists|..|`. [I]
- Pain: SMT trigger tuning, matching loops and `exists` witnesses need explicit `assert(... )` hints; recursion over `Seq` needs `decreases` and lemma calls (`reveal`, `assert_seqs_equal!`); non-reproducible rlimit failures when a lemma set grows. Our laws (uniqueness of a relation by induction over byte lists, split-invariance of a stream decoder) are inductive proofs that are fine in Verus but need hand-written lemmas, not push-button [I].
- No dependent-type/computation-in-proof option: you cannot `decide` over 256 byte values; use `assert(...) by (bit_vector)` / `by (compute)` [I].

**vstd UTF-8**
- vstd has a `utf8` module of ~110 specs/lemmas: `encode_utf8`, `decode_utf8`, `valid_utf8`, `partial_valid_utf8`, `is_char_boundary`, `decode_first_scalar`, `utf8_byte_ranges_bitwise`, ... [V: https://verus-lang.github.io/verus/verusdoc/vstd/utf8/index.html]. These are for *valid* UTF-8 (encode/decode of well-formed sequences) and *do not* include maximal-subpart/U+FFFD replacement as far as the listing shows [V: same page; replacement not in list]. Warn the agents: do not import it into the trusted spec (spec should remain independent), but it is a useful comparison and lemma source (e.g. byte-range tables). The page does not say which are executable. [V partial]
- smoothutf8's `spec::is_valid_utf8` is a direct transcription of Unicode Table 3-7 and its Verus proof is about validity only, not replacement. [V: docs.rs page]

**Theorem shape**: Hoare-style `ensures` on an exec Rust function: for all inputs `input@`, `state@`, result relates to the Verus-level spec; panic freedom/overflow-freedom included; streaming property stated as ensures on the step function over ghost state plus a separate proof fn for "any split" by induction over buffer lists [I].

**Trusted between theorem and running Wasm** [I unless noted]
1. Verus + Z3 (SMT; "Verus is not foundational — trusts Z3 and its encoding") [V: smoothutf8 page; V: tcb.md https://raw.githubusercontent.com/verus-lang/verus/main/source/docs/guide/src/tcb.md lists assumes, axioms, external_body, external].
2. Verus's Rust semantics encoding (a modified rustc front end, ghost erasure).
3. rustc/LLVM wasm32 backend, `core` library.
4. The `extern "C"` shim and any `external_body` helpers, JS wrapper and the Wasm engine.
5. The spec itself (translated by hand from LAWS.bend).

**Biggest risk**: the quantifier-heavy existence/uniqueness laws in SMT: flaky proofs and trigger issues. Second: the no_std/wasm story is only inferred from one third-party crate (small, 1 star, 4 months old).

**Agent feasibility: HIGH** (best among source-level candidates). Rationale: prebuilt binary, seconds-scale feedback, very close published precedent (UTF-8 validator, no_std, wasm32 CI), Rust is a language agents write fluently, benchmarks show LLM proof generation works on Verus (AutoVerus >90% of 150 tasks [V: https://arxiv.org/abs/2409.13082]; VeruSAGE-Bench 849 tasks incl. system projects, hands-off agent setups with Claude Sonnet 4/4.5 [V: https://arxiv.org/pdf/2512.18436v2]; numbers for current models not retrieved).

---------------------------------------------------------------------------------------------

## 2. Aeneas + Charon (Rust -> Lean 4)

**Links / dates**
- https://github.com/AeneasVerif/aeneas ; latest commit 2026-11-09 ("Update to leanprover/lean4 v4.36.0 rc2") [V: https://api.github.com/repos/AeneasVerif/aeneas/commits].
- Charon https://github.com/AeneasVerif/charon ; pinned Rust `nightly-2026-09-17` with rustc-dev, llvm-tools, miri [V: https://raw.githubusercontent.com/AeneasVerif/charon/main/charon/rust-toolchain].
- Lean pin: `leanprover/lean4:v4.36.0-rc2` (a release candidate) [V: https://raw.githubusercontent.com/AeneasVerif/aeneas/main/backends/lean/lean-toolchain].

**Install**
- README says build from source (opam OCaml 5 + charon pin via rustup or nix, `make`) and doesn't mention binaries [V: README https://raw.githubusercontent.com/AeneasVerif/aeneas/main/README.md], but GitHub has **daily prerelease nightlies** `nightly-2026.11.10-0d21a9e` with `aeneas-linux-x86_64.tar.gz` and `lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz` (prebuilt Lean library) [V: https://api.github.com/repos/AeneasVerif/aeneas/releases]. Nix: `nix run github:aeneasverif/aeneas` [V: README].
- Estimate [I]: with nightlies + elan: 10-20 min; building from source (opam, rustc-dev nightly, OCaml): 30-60+ min, 8 GB RAM comfortable; Mathlib-free? Aeneas lean lib depends on Mathlib-ish pieces (the aeneas-lean build archive exists to avoid recompiling) [I].

**Rust subset** [V: README + https://arxiv.org/html/2609.15648]: safe Rust only; loops are translated to recursive functions; nested borrows, traits, iterators supported; slices and arrays modelled as Lean subtypes of lists; `assert!` becomes a proof obligation; unsafe, raw pointers, interior mutability, concurrency unsupported. README limitations (may be stale): `return` inside nested loops and `break/continue` to outer loops unsupported; generic instantiation with `&mut` not supported [V: README]. Charon limitations doc says unsupported features are tracked in its issue #142 and the tool is beta [V: https://raw.githubusercontent.com/AeneasVerif/charon/main/docs/limitations.md]. Ruled out for us: no_std/wasm target handling by Charon is undocumented [unverified]; it should not matter, since we only extract the safe core and compile the same source with rustc separately [I].

**Proof automation**: `progress` / newer `step`, `step*`, `scalar_tac`, `simp_scalar`, `simp_lists`, `bv_tac`, `decompose` [V: https://arxiv.org/html/2609.15648 ; newsletter https://aeneasverif.github.io/newsletter/2025/04/07/aeneas-newsletter.html]. Lean's kernel with `decide`/`omega`/`grind`/`bv_decide` lets agents do case analysis over bytes more easily than SMT (`bv_decide` trusts an external SAT certificate checker/LRAT, `native_decide` extends the TCB) [V partly: paper lists these in TCB].

**Evidence for agents**: Sept 2026 paper "Scaling Verification of Cryptographic Software with Aeneas, Rust, and Lean": 237 KLOC Lean for 16.7 KLOC Rust (~14:1), agents wrote most proofs (Claude Opus 4.6-5.0, GPT), Opus 5 closed all seven benchmark proofs; reported pain: staged campaigns, models sometimes try to weaken goals [V: https://arxiv.org/html/2609.15648]. Also May 2026 experience report with AI provers, listing Lean toolchain drift between tools as a pain point [V: https://arxiv.org/abs/2605.30106]. Runtime Verification verified a Linux Binder byte-deserializer this way (panic-freedom for all byte inputs) [V via search: https://runtimeverification.com/blog/verifying-linux-rust-code-from-binder-to-lean4].

**Spec language fit**: Lean 4 is the best spec language of this group for our style (inductive relations, `∃`, `∃!`, lists, `decide`); the spec could even be written as inductive predicates over `List UInt8` and be near-literal from the Bend laws [I].

**Theorem shape**: Lean theorem about the *pure monadic translation* (`Result`-valued functions) of the Rust function, e.g. `step state input = ok (state', out) ∧ Spec ...` for all inputs, including no-panic [I; V for the Result style: paper].

**Trusted** [V: https://arxiv.org/html/2609.15648 for items 1-3, 5; rest I]
1. rustc (MIR) and its wasm backend (paper lists rustc + x86/AArch64 backends; Wasm analog [I]).
2. Charon (MIR extraction) and Aeneas translation (paper proofs of the translation at ICFP'22 / ICFP'24 on a core calculus, not a mechanization of the implementation) [V: README refs].
3. Lean kernel; `native_decide` / `bv_decide` if used.
4. Aeneas axioms for std functions used (keep to `core` basics).
5. Specs and main theorem statements.
6. Unsafe `extern "C"` shim, JS, engine.

**Biggest risk**: toolchain churn (Lean RC pin, nightly Rust pin, daily prerelease binaries only), and restrictions on loop control flow forcing awkward code shape (rewrite as state machine with no early exit in nested loops, which suits a streaming decoder anyway [I]).

**Agent feasibility: HIGH-MEDIUM.** Strongest source-level proof language and strong evidence of agents succeeding; heavier install and version fragility than Verus. Proof sizes are larger (but "long proofs are fine").

---------------------------------------------------------------------------------------------

## 3. F* / Low* with KaRaMeL Wasm backend

- Repo https://github.com/FStarLang/karamel ; active (latest commits 2026-11-08, mostly Rust backend/misc) [V: commits API]. Wasm files `lib/CFlatToWasm.ml`, `OptimizeWasm.ml`, `SimplifyWasm.ml` exist; the last commit touching `CFlatToWasm.ml` is 2026-05-03 (refactors; earlier substantive history not checked) [V: https://api.github.com/repos/FStarLang/karamel/contents/lib ; commits?path=lib/CFlatToWasm.ml].
- HACL* still regenerates `dist/wasm` (commits 2026-10-12, 10-14, 10-27: "wasm gets more optimized") [V: https://api.github.com/repos/hacl-star/hacl-star/commits?path=dist/wasm]. HACL* README says it is in *maintenance mode* [V: https://raw.githubusercontent.com/hacl-star/hacl-star/main/README.md]. So the backend is **alive but passively maintained**.
- F* releases weekly with Linux x86_64 binaries (v2026.10.25) [V: https://api.github.com/repos/FStarLang/FStar/releases]. KaRaMeL via `opam install karamel` or `make` (needs OCaml >=4.10, menhir, sedlex, zarith, wasm>=2.0.0, an F* binary) [V: https://raw.githubusercontent.com/FStarLang/karamel/master/README.md]. Estimate [I]: 30-60 min, ~8 GB RAM (opam builds), plus Z3 4.8.5/4.13 managed by F*.
- What is proved about Low*->Wasm: the S&P'19 paper "Formally Verified Cryptographic Web Applications in WebAssembly" formalizes the translation rules and implements them in a few thousand lines of OCaml; abstract makes no claim of a mechanized compiler-correctness proof [V: https://www.microsoft.com/en-us/research/publication/formally-verified-cryptographic-web-applications-in-webassembly/]. I could not fetch the paper body (core.ac.uk 403, HAL blocked), so whether there is a paper proof is **not established**. Inference: no mechanized proof; the Wasm output is trusted [I]. Low*->C has pen-and-paper arguments (POPL'17 "Verified low-level programming embedded in F*" https://arxiv.org/pdf/1703.00053 [V exists; content not read]).
- Model constraints [I]: Low* is a first-order, C-like subset: buffers/pointers in a stack/heap region, no closures after extraction, monomorphised, machine integers (`UInt8`, `UInt32`), loops via `C.Loops` combinators. Fine for a byte decoder; Wasm output uses linear memory and (I recall) a shadow stack for address-taken locals.
- JS boundary: HACL-Wasm used a generated JS loader with a hand-written API layer for buffers [I]; our decoder state would be a Low* struct/buffer pointer.
- Spec fit: F* has `list`, refinement types, `exists`, SMT (Z3) + tactic; specs in `Type0` with `squash`. Existence/uniqueness are doable but proofs are SMT-style like Verus with more friction (fuel/ifuel, universe, `--z3rlimit`) [I].
- Trusted [I]: F* + Z3, Low* memory-model axioms, KaRaMeL (esp. CFlatToWasm and the Wasm printer), JS wrapper, engine.
- Biggest risk: toolchain complexity and agent unfamiliarity with Low*; sparse docs for Wasm path specifically (HACL* dist is the only worked example).
- **Agent feasibility: MEDIUM-LOW.** Less proof reach than hoped (compiler step unverified), heaviest install of the SMT group, and Rust/Verus gives the same level of assurance with an easier language.

---------------------------------------------------------------------------------------------

## 4. Lean 4 compiled to Wasm (Lean -> C -> emcc/WASI)

- Lean reference platform page lists "Emscripten WebAssembly" as Tier 2 ("cross-compiled but not tested by CI... may be silently broken") [V: https://lean-lang.org/doc/reference/latest/platforms/]. A Zulip report says wasm32 release assets stopped after v4.15.0 and wasm32 is "in the code but broken" [V via search: https://leanprover-community.github.io/archive/stream/113488-general/topic/Newer.20version.20of.20Lean.20with.20WASM.3F.html ; snippet only]. 2023 thread: single-threaded hello world worked, threaded and 32-bit builds flaky [V: https://leanprover-community.github.io/archive/stream/270676-lean4/topic/wasm.20build.html]. WASI: "cannot compile the runtime to wasm32-wasi" due to POSIX dependencies (2023) [V via search snippet].
- Third-party: `T-Brick/lean2wasm` (last push 2024-03-17, 29 stars) [V: https://api.github.com/repos/T-Brick/lean2wasm]; `xeus-lean` compiles the whole runtime to Wasm with Emscripten Memory64 (patched single-threaded runtime) [V via search: https://github.com/Verilean/xeus-lean].
- What would work in principle [I]: write the decoder as a Lean function over `ByteArray`/`UInt8` with `@[export]`, `lake` emits C, compile C + `lean.h` + the Lean runtime (`libleanrt`, needs malloc, ~hundreds of KB, no GC but ref counting) with emcc to standalone Wasm. Lean's runtime depends on libc and (even single-threaded) C++; you would have to build and patch it yourself. Runtime size and allocation behavior (boxed lists, RC) mean a streaming decoder over `ByteArray` is ok but not tiny.
- What is trusted [I]: Lean kernel (theorem about the Lean function as a mathematical term), then the **unverified Lean compiler** (LCNF -> IR -> C; known to be separate from the kernel, with `@[implemented_by]`/`@[extern]`/`unsafe` escape hatches), Lean runtime in C, emcc/LLVM, JS glue. Largest unverified gap in the list: the compiler is large and the runtime is a C++ library.
- Biggest risk: build/toolchain broken at current Lean versions; nobody to ask.
- **Agent feasibility: LOW-MEDIUM** (proofs would be delightful in Lean, delivery is the problem). A hybrid (Lean spec + Lean impl proven, then Lean->C->Wasm) is what this is; compare with Aeneas, which gives Lean proofs with a *Rust* delivery path that already works.

---------------------------------------------------------------------------------------------

## 5. Rocq extraction routes and Dafny (brief)

**Rocq (9.3.0, 2026-09-18 [V: https://api.github.com/repos/rocq-prover/rocq/releases])**
- Route A: extraction to OCaml, then `wasm_of_ocaml` (part of js_of_ocaml; release 6.5.0 on 2026-10-22 [V: https://api.github.com/repos/ocsigen/js_of_ocaml/releases]; requires Binaryen >= 120 [V: README]; relies on Wasm GC and engine support, Node version not confirmed). Result: big runtime (OCaml GC in Wasm GC), JS boundary uses OCaml values/strings (awkward `Uint8Array` conversion), extraction (paper proof, mostly trusted; MetaRocq verified erasure exists but not the OCaml extractor) + OCaml compiler + wasm_of_ocaml all unverified. Not worth it. [I]
- Route B: CertiCoq-Wasm (verified Gallina -> Wasm, mechanized w.r.t. WasmCert-Coq, CPP 2025) [V: https://popl25.sigplan.org/details/CPP-2025-papers/9/CertiCoq-Wasm-A-verified-WebAssembly-backend-for-CertiCoq]. This is on the *other* agent's list; noted only because it is the strongest end-to-end story I found. Feb 2026 ANF-pass proof was done with Claude Code assistance [V via search snippet: emergentmind CertiCoq summary].
- Verdict: A not worth considering; B belongs to the other survey.

**Dafny**
- Backends: C#, Java, Go, Python, JS, and an experimental Rust compiler (4.7.0 notes call it "experimental"; paper "Performant Readable and Interoperable Rust from Dafny", Dafny'25) [V via search: https://newreleases.io/project/github/dafny-lang/dafny/release/v4.7.0 ; https://popl25.sigplan.org/details/dafny-2025-papers/14/]. Nothing found for Wasm. Dafny output runs a big runtime (BigInteger, `Sequence`) with the JS backend, which doesn't give us Wasm at all; Rust backend then rustc to wasm is possible but unproven, adds `dafny-runtime` crate. Trusted: Dafny compiler + Boogie + Z3 + the Rust runtime. [I]
- Verdict: Not worth considering; Verus gives the same SMT-auto-active workflow directly on Rust.

---------------------------------------------------------------------------------------------

## 6. Other candidates found

- **Creusot** (Rust -> Coma/Why3, SMT + interactive Coq/Isabelle fallback): needs rustup + opam + `./INSTALL`; cannot verify raw pointers (fine for a safe core). Same TCB shape as Verus (Why3 + solvers + rustc), supports Why3 interactive provers for the hard induction. Install heavier than Verus [V: https://github.com/creusot-rs/creusot ; limitations from v0.1 notes via search]. Runner-up to Verus in the SMT group; release dates not retrieved. Feasibility MEDIUM.
- **RefinedRust** (Rocq/Iris) was used alongside Verus in smoothutf8 for unsafe leaf loads [V: docs.rs page]. Heavy, Rocq-based, small user base. Not recommended.
- **Hax (Cryspen)**: Rust -> F*/Rocq/Lean like Aeneas; paper 2605.30106 used Hax and Aeneas together [V]. Same layer as Aeneas; no advantage found.
- **CakeML**: no Wasm backend found [V via search: native targets only].
- **No small, verified compiler to Wasm for a convenient language** (other than CertiCoq-Wasm and the mechanized Wasm semantics, which are the other agent's scope) was found. I did not search for translation-validation of rustc output to Wasm, nor for Wasm-targeting Isabelle/HOL code generators; coverage is weak here.

---------------------------------------------------------------------------------------------

## Comparison on the three criteria

| | Simplicity (layers) | Proof reach / trusted | Agent difficulty |
|---|---|---|---|
| Verus | Rust source -> rustc -> Wasm; theorem on the same Rust text | Z3, Verus encoding, rustc, unsafe shim; SMT not foundational | Easiest: 36 MB binary, fast feedback, UTF-8 validator precedent |
| Aeneas | Rust -> Charon -> Aeneas -> Lean; rustc compiles the same source | Lean kernel (foundational) but + Charon/Aeneas (paper-proved), rustc | Larger proofs, daily nightlies, Lean RC pin, strong AI-agent evidence |
| F*/KaRaMeL | Low* -> KaRaMeL -> Wasm | Z3, F*, KaRaMeL Wasm printer (unverified) | Heavy install, Wasm path in maintenance |
| Lean->C->Wasm | Lean -> C -> emcc | Kernel + unverified Lean compiler + runtime | Wasm build of Lean runtime broken/Tier 2 |
| Rocq/OCaml/wasm_of_ocaml | many layers | extraction + OCaml + wasm_of_ocaml | not worth it |
| Dafny | Dafny -> Rust -> Wasm | experimental backend | not worth it |

## Ranking (for an agent-driven attempt)

1. **Verus** - fewest layers, easiest install, directly relevant precedent (smoothutf8: no_std, Verus-verified, wasm32 CI), fast SMT feedback. Weakness: SMT triggers for existential/uniqueness laws; no foundational kernel.
2. **Aeneas + Charon + Lean** - best spec language and proof kernel, demonstrated agent-driven verification at scale (14:1 proof:code), but more toolchain churn and one more translation layer (Charon/Aeneas) in the TCB; loop-control restrictions.
3. **Creusot** - Verus-like but heavier install; interactive Coq/Isabelle fallback is its edge.
4. **F*/Low*/KaRaMeL Wasm** - real, still-regenerated Wasm backend but compiler step not mechanized and heavy tooling.
5. **Lean -> C -> Wasm** - nice proofs, broken/unsupported delivery, largest unverified compiler.
6. **Dafny**, 7. **Rocq extraction + wasm_of_ocaml** - not worth considering. (CertiCoq-Wasm is another agent's scope and should be compared separately.)

## Not established
- Whether Verus works for `wasm32-unknown-unknown` beyond the smoothutf8 precedent; whether `cargo verus build --target wasm32-...` works (untested).
- Whether the Low*-to-Wasm translation has any proof (paper body not retrievable).
- Install times/RAM for all (inferences only).
- Current Aeneas status on `break`/`continue`/`return` in nested loops (README may be stale).
- Whether Lean's own Emscripten build works at v4.36 for standalone programs.
