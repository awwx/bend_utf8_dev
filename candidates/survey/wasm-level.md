# Survey: candidates whose final theorem is about a WebAssembly module

Date of survey: 2026-11-11. Read-only research: nothing was installed, built or run; repositories were
shallow-cloned and read only. All "last commit" dates come from `git log` in those clones or the GitHub API.

Tagging convention: **[V: source]** = verified from a primary source (repo file, README, opam file, paper,
GitHub API); **[I]** = my inference (flagged so a reader can discount it). Anything I could not establish is
listed in the "Open questions" section at the end.

Target of the experiment: a hand-written Wasm module (streaming UTF-8 decoder, loops over linear memory,
state across calls, maybe `wasm:js-string` builtins) run in Node 26, theorem = functional correctness stated
against a relational spec (existentials over byte lists, uniqueness, "for any split into buffers").

---------------------------------------------------------------------------------------------------

## 0. Executive comparison

| | Wasm version mechanised | GC arrays / host imports | Program logic usable *today* | Binary `.wasm` bytes covered by theorem? | Toolchain risk |
|---|---|---|---|---|---|
| **Talos** (Lean 4) | 3.0-ish: core + SIMD + bulk mem + ref types + GC (struct/array/i31) + exceptions + tail calls [V] | yes / yes (`HostFn : Store -> args -> HostResult`, store includes `gcHeap`) | yes: WP calculus in repo, migrating to iris-lean small-step [V] | no: `.wasm` -> `wasm-tools print` -> Lean WAT parser (trusted) [V] | medium (young, AGPL, Mathlib dep, API churn) |
| **WasmCert-Coq** (Rocq) | 2.0 + subtyping + tail-call; no GC [V] | no GC / host = typeclass relation [V] | no (Iris-Wasm is on older 1.0 fork) [V] | no: binary parser/printer unverified, no round-trip theorem [V] | low (CI on Rocq 9.0, 9.1, 9.2) |
| **Iris-Wasm** (Rocq) | 1.0 only [V] | no / host-language model in logic | yes (stack-module examples) | no | medium-high (stale since Jan 2025, Coq 8.20-era pins) |
| **WasmCert-Isabelle** | 2.0 (ref types, bulk mem); no GC [V] | no / `host_func_apply` relation | no (Wasm Logic of 2019 is not public/ported) [V/I] | no: parser is external OCaml [V] | low-medium |
| **CertiCoq-Wasm** (Rocq) | emits 2.0+tail-call subset, strict-1.0 mode [V] | no (no GC; GC variant is unverified) | n/a: it is a compiler | no | high (pinned unreleased MetaRocq, 50-90 min CI) |
| **lean-wasm** (T-Brick) | core only; vectors missing, floats partial [V] | n/a | none | has a Lean binary decoder [V] | n/a |
| **KWasm** (K) | 1.0 [I] | no | K reachability proofs (not a proof assistant) | binary parser added Jul 2026 [V] | high for agents |
| **SpecTec -> Rocq/Isabelle/Lean** | would be 3.0 | n/a | none | n/a | not available |

Ranking at the end of the file.

---------------------------------------------------------------------------------------------------

## 1. WasmCert-Coq (Rocq)

### Links and activity
- Repo: https://github.com/WasmCert/WasmCert-Coq (branch `master`). Last commit **2026-10-12** ("added a guard for Parray.set_gen, and wrote changelogs (#100)"); 1461+ commits [V: git log; README page].
- opam package `coq-wasm` **2.2.1**, published 2026-10-20 [V: https://rocq-prover.org/p/coq-wasm]. Earlier versions 2.2.0, 2.1.0, 2.0.3, 2.0.2, 2.0.1, 0.2, 0.1 [V: same page].
- A `v2.3.0-test` branch/tag had CI runs on 2026-10-13 [V: GitHub Actions API].

### Wasm version
- README: "formalises Wasm version 2.0 with the following additions: subtyping systems (from the future funcref/GC extension proposals); tail-call". SIMD execution is delegated to opaque opcodes calling the OCaml reference implementation [V: https://github.com/WasmCert/WasmCert-Coq README; `changelogs/v2.0.md`].
- Wasm 2.0 includes multi-value blocks, reference types, multiple tables, bulk memory/table ops [V: `changelogs/v2.0.md`].
- **No GC**: grep of `theories/datatypes.v` finds no `struct`, `array`, `i31` type or instruction constructors [V: my grep of the clone]. The subtyping machinery is a forward-looking shell with no non-trivial subtype relations between current value types [V: `changelogs/v2.0.md`].

### Dependencies and install
- `coq-wasm.opam` (2.2.1): `coq >= 9.0 & < 9.3~`, `coq-compcert >= 3.14`, `coq-flocq >= 4.1.0 & < 5~`, `coq-ext-lib`, `coq-mathcomp-ssreflect >= 2.4.0 & < 2.7~`, `rocq-parseque >= 0.2.0`, `wasm = 2.0.2` (the OCaml reference interpreter, used for text/wast parsing), `zarith`, `dune >= 3.17`, `cmdliner` [V: opam file in clone]. **No Iris** dependency in master [V].
- Install: `opam repo add coq-released https://coq.inria.fr/opam/released; opam install .` [V: README]. Opam release also works: `opam install coq-wasm` [I: from the package page].
- Build cost: README says "at least 8 GB of RAM" [V]. CI "Test compilation" runs take 11-14 minutes wall clock on GitHub runners [V: Actions API, runs of 2026-10-12/13]; Nix CI for Rocq 9.0/9.1/9.2 3.4-4 min (cached deps) [V]. My estimate for a cold local build including CompCert + mathcomp: 30-60 min, peak RAM 4-8 GB [I].
- CI covers Rocq 9.0, 9.1, 9.2 (`nix-action-9.{0,1,2}.yml`) [V].

### Binary printer / parser
- `theories/binary_format_printer.v` (690 lines), `binary_format_parser.v` (1353 lines), `leb128.v`, plus `text_format_parser.v` [V].
- README: "experimental work on a parser for the binary format which is currently **unverified**" [V].
- There is **no round-trip theorem**. Only concrete tests such as `run_parse_module (binary_of_module m) = Some m` proved by `vm_compute; reflexivity` for six hand-made modules in `binary_format_tests.v`. A `binary_format_spec.v` stub existed with a commented-out `encode_decode_is_identity` TODO (deleted from master in commit "Misc updates for Rocq 9.x", still a stub in the Iris-Wasm repo) [V: clones].
- Printer emits 1.0-compatible binaries when only 1.0 features are used [V: `changelogs/v2.0.1.md`].

### Interpreter, extraction, instantiation, host
- Verified interpreter (WasmRef-Coq) with soundness w.r.t. the relational semantics, "proof carrying interpreter deriving progress", type checker with soundness and completeness, type preservation/progress, instantiation soundness (`instantiation_sound.v`, `interp_instantiate_sound.v`) [V: README component list; file list].
- Extracted `wasm_coq_interpreter` passes the official Wasm 2.0 core testsuite (SIMD excluded in earlier releases; v2.2.0 notes SIMD via reference eval) [V: README, `changelogs/v2.0.3.md`, GitHub releases page via search].
- Host model: `Class host` with `host_state` and a relation `host_application : host_state -> store -> function_type -> host_function -> seq value -> host_state -> option (store * result) -> Prop`; with three axioms (store extension, store typing preserved, results respect types). `host_function` is abstract (`host_function_class`). Non-deterministic and possibly diverging [V: `theories/host.v`]. So an imported JS function can be stated as a host-application relation you supply, but it must be a relation over the *Wasm 2.0 store*, which has no GC heap.
- Memory is abstracted behind `Class Memory` / `BlockUpdateMemory` (list and persistent-array implementations); proofs go through the interface [V: `theories/memory.v`, `changelogs/v2.0.3.md`].
- Semantics is a small-step reduction relation `reduce` (opsem.v) with `reduce_trans`; instantiation defined as a relation `instantiate` in `instantiation_spec.v` [V].

### Program logic: Iris-Wasm
- README of WasmCert-Coq: the program logic lives on a **separate branch** `iris-wasm-opam`, "migrated from an older build for the artefact ... PLDI'23"; "a more updated version working with opam" is https://github.com/logsem/iriswasm [V: README].
- `iris-wasm-opam` branch last commit **2023-10-24** ("removed cmdliner") [V: GitHub API]. It is **not merged into and not compatible with** current master: Iris-Wasm is built on the Wasm **1.0** mechanisation, with its own copies of `datatypes.v`, `opsem.v`, with an extra `AI_call_host` instruction [V: iriswasm README, "Our work uses the mechanisation of WebAssembly 1.0 by Watt et al... slight reformulation of the host function implementation"].
- See section 2 for Iris-Wasm itself.
- Newer: Iris-WasmFX (PLDI 2026) "WasmFXCert, a Rocq mechanisation of WasmFX ... built atop the existing WasmCert" and a program logic extending Iris-Wasm; repo `logsem/iris-wasmfx` [I: only from search-result snippets of https://dl.acm.org/doi/10.1145/3808271 (HTTP 403 when fetched) and PLDI listing]. Suggests Iris-Wasm is being kept alive in the Aarhus group, but I did not confirm it targets 2.0 master.

### How would one prove a loop-over-memory module here?
[I] Directly, without a program logic: state a Hoare-style triple over `reduce_trans` (for fully reduced configurations with `frame`, `label` contexts), prove a loop-invariant lemma by induction on the remaining input length, use `lfilled`/context lemmas from `contexts.v` for `br`/`loop`, and the `Memory` class lemmas for load/store. CertiCoq-Wasm is the existing evidence that this style scales: 6050 + 5137 + 2118 + 3512 lines of Rocq proof for `translate_body_correct`, primitive ints, instantiation and utilities (see section 3), but there the loops are tail calls, not `loop` blocks. Expect the agent to first build a small wp/Hoare layer (several thousand lines) or port Iris-Wasm's rules.

### The end-to-end theorem for our decoder
```
Theorem decoder_correct :
  forall (s : store) (inst : instance) ...,
    instantiate empty_store decoder_module [] (...) ->      (* or: after running instantiation *)
    forall st buf, Spec.valid_state st -> ...
      exists s' out st', reduce_trans (hs, s, frame_with_args, [invoke f_decode ...]) (hs, s', f, [values]) /\
        mem_contents s' out_region = spec_output ... /\ state_repr s' st'
```
plus the three LAWS (any split / safe / prompt) lifted to Wasm configurations. The theorem is about the **Wasm syntax tree** `module` under the formal 2.0 semantics. The bytes of the `.wasm` are linked only by the unverified printer/parser (workable mitigation [I]: check `run_parse_module (binary_of_module m) = Some m` by `vm_compute` for the one concrete module, which pins parser output to the proved AST for those exact bytes; still trusts the parser's agreement with the binary spec).

### Smallest existing verified program
None in master. Closest: Iris-Wasm's examples (below) and CertiCoq-Wasm's generated-code proofs.

### Biggest risk
No program logic for the 2.0 semantics; every proof infrastructure piece (frames, labels, `loop`/`br` reasoning, memory framing) must be built by the agent. Also no GC arrays.

### GC arrays / `wasm:js-string`
Outside the formal semantics: no array types, so `fromCharCodeArray : (ref null (array (mut i16))) ...` cannot even be typed [V: no GC in datatypes.v]. A decoder that exposes only linear memory (JS side does `TextDecoder`/`String.fromCharCode`) is in scope.

### Feasibility for an agent-driven attempt: **medium** (toolchain solid, proof infrastructure missing).

---------------------------------------------------------------------------------------------------

## 2. Iris-Wasm (Rocq, program logic on Wasm 1.0)

- Repo: https://github.com/logsem/iriswasm; last commit **2025-01-30** ("fixed outdated language in the README"); GitHub `pushed_at` 2025-05-02; 4 stars [V: git log, API].
- Needs `coq >= 8.20.1` (no upper bound), `coq-iris >= 4.3.0`, `coq-stdpp >= 1.11.0`, `coq-compcert >= 3.15`, `mathcomp-ssreflect >= 2.3.0`, `coq-parseque`, `coq-itree`; OCaml 4.14.2 recommended [V: opam file, README]. Whether it still builds on Rocq 9.x with current Iris is unknown [open question].
- Build: "requires at least 8GB of RAM and may take over 30 minutes" [V: README].
- Proof rules for pure ops, control (block/loop/br), memory (load/store), calls, structural/bind rules, trap rules; adequacy theorem w.r.t. the 1.0 operational semantics; host language and module instantiation lemma; logical relation for robust safety [V: README structure section].
- Examples: `iris_examples.v` (378 lines), factorial via Landin's knot (1045), and the stack module: ~200 lines of Coq define the module (637-byte binary); ~2100 lines verify the individual function specs; stack example total 8787 lines incl. clients and robustness [V: Rao thesis https://www.doc.ic.ac.uk/~pg/publications/Rao2025Designing.pdf ch. 5; iriswasm README "11541 = 2754 + 8787"]. Thesis explicitly says this reflects "a version of Iris-Wasm without a bespoke proof mode" [V]. Total development 51,497 lines of Coq (cloc) [V: thesis Fig 5.6].
- Lines of code of the Iris-Wasm theory vs. the loop-heavy decoder: the specs are separation-logic with explicit memory points-to resources (`N.of_nat m ↦[wmlength]`), so byte-array reasoning in a loop requires you to manage ownership of the input and output regions; no loop-over-array example in the repo's examples that I saw [I].
- Theorem shape: `wp` triple, adequacy gives "program runs safely w.r.t. official 1.0 semantics" (partial correctness: ends in value or diverges/does not get stuck) [V: thesis]. Termination would have to be proved separately [I].
- Binary: the Iris-Wasm repo has binary parser/printer, again unverified with a TODO round-trip stub [V].
- GC / js-string: outside (1.0) [V].
- Feasibility: **low-medium**. Good example of the *kind* of logic needed, but stale, 1.0-only, and the proof-mode is raw. Best use: take the rule shapes (`wp_loop`, `wp_load`, `wp_store`) as a template for a home-grown logic on the 2.0 semantics [I].

---------------------------------------------------------------------------------------------------

## 3. CertiCoq-Wasm / CertiRocq (verified Wasm backend)

### Links and activity
- Repo: https://github.com/CertiRocq/certirocq, branch `main`. Last commit **2026-11-03** (merge of #182 "Fix gmp ffi"); 18-24 open issues; very active in Oct-Nov 2026 (uncurry proof rewrite, bootstrap, primitive values, MetaRocq 9.1 adaption) [V: git log, GitHub API].
- Open Wasm PRs: #183 "CodegenWasm: export table" and #184 "allocate constructors with store offsets" (2026-11-06) [V: GitHub PR list].
- Paper: Meier, Jensen, Pichon-Pharabod, Spitters, "CertiCoq-Wasm: A Verified WebAssembly Backend for CertiCoq", CPP 2025 [V: https://www.cl.cam.ac.uk/~jp622/certicoq-wasm.pdf; https://popl25.sigplan.org/details/CPP-2025-papers/9/CertiCoq-Wasm-A-verified-WebAssembly-backend-for-CertiCoq].
- `rocq-certirocq.opam` is `dev+9.0`-versioned, not on opam-released; install is from source [V].

### What is the theorem
`theories/CodegenWasm/toplevel_theorem.v`, `LambdaANF_Wasm_related` [V]: for a **closed** LambdaANF expression `e` that evaluates (`bstep_e`) to `v`, and a successful `LambdaANF_to_Wasm` compilation to `module`, there exist `sr, fr` such that `instantiate' module hs sr fr` and `reduce_trans (... [AI_basic (BI_call main_function_idx)]) (... [])` reaching `sr'` where the global `result` holds a Wasm representation of `v` (`result_val_LambdaANF_Wasm`) -- *or the execution ran out of memory* (paper: "or the execution ran out of memory") [V: paper section 2.2; the `out_of_mem` global in `LambdaANF_to_Wasm.v`]. Note: the Rocq statement quoted above has no out-of-memory disjunct in its conclusion; the OOM case is handled through the `min_available_memory` / restrictions assumptions and `glob_out_of_mem`. I did not fully reconcile paper and statement [open question].
- Assumptions: primitive environment well-formed; constructor environment restricted (`max_constr_args = 1024`, `max_num_functions = 1_000_000`, ordinal < 2^31, `max_function_args = 100`); unique bindings; closed [V: `LambdaANF_to_Wasm_restrictions.v`].
- Proof size in `CodegenWasm`: ~19,000 lines of Rocq (6050 `_correct`, 5137 `primints_correct`, 3512 utils, 2118 instantiation, ...). **No `Admitted` in CodegenWasm** [V: grep].
- Target semantics: WasmCert-Coq (2.0 + tail call). Output uses Wasm 1.0 + tail calls, strict-1.0 mode available [V: paper].

### Verified vs. trusted pipeline
Pipeline: Gallina -> (MetaRocq reification + erasure) -> LambdaBox -> LambdaANF -> LambdaANF optimisations -> Wasm [V: paper Fig. 1; README directory notes].
- MetaRocq stage: trusted (dotted orange in Fig. 1) [V: paper].
- LambdaBox -> LambdaANF: ANF conversion proved (`anf_correct.v`, `anf_divergence.v`); CPS conversion "not yet proved correct" [V: `theories/LambdaBox_to_LambdaANF/README.md`].
- LambdaANF optimisations: "large parts verified ... others in the process of being verified" [V: README]. In `main`, `merge_dup_funs_correct` is `Admitted` (`LambdaANF/toplevel_theorems.v`); the combined `metarocq_anf_pipeline` end-to-end lemma is commented out and contains `admit`s in `Compiler/correctness.v` [V: files]. The paper says: "Once CertiCoq has an end-to-end correctness theorem linking its verified stages, we can combine our result with CertiCoq's internal correctness to get a Gallina-to-Wasm result" [V: paper s2.2] -- i.e. the Gallina-to-Wasm chain is *not* closed.
- Wasm printing to bytes: the generated module is a Wasm syntax tree; binary encoding goes through WasmCert-Coq's printer (unverified) [V/I].
- Primitive integers (63-bit Uint63): supported as i64 operations; verified (found a corner case unsoundness in Coq's `vm_compute`) [V: paper abstract].

### Data across the boundary (the key problem)
- The module exports `main_function` (no params), globals `result` (i32 pointer) and `out_of_mem`, `memory`, plus one export per Coq function (debug names) [V: `LambdaANF_to_Wasm.v` export list; test harness `tests/wasm/js/run_wasm.js` calls `obj.instance.exports.main_function()` then reads `result` and `out_of_mem` and pretty-prints with `modules/pp.js`].
- The correctness theorem is for **closed programs**: no argument can be passed in. So to run the decoder on JS-provided bytes you would need unverified glue that serialises a Coq `list`/`N` value into the module's constructor memory layout and calls an exported function, which is outside the theorem [I]. The paper's own JS case study (SHA-256 web page) and the Concordium smart contract use hand-written, unverified glue ("the generated smart contract can only go wrong due to a mistake in the glue code") [V: paper s4].
- Repeated calls: `main_function` can be called again but memory/gmp is never reset; no theorem about repeated calls [I]. Streaming state across calls would have to live in unverified JS or in Wasm memory managed by the glue.
- Memory: **no GC**; bump allocation pointer `gmp` never decreases; on exhaustion sets `out_of_mem := 1` and aborts; max 1920 MB [V: paper s2.1.1, `LambdaANF_to_Wasm.v`]. A WasmGC variant exists but is explicitly unverified [V: paper].

### Install / build / compatibility
- INSTALL.md: opam switch with `ocaml-base-compiler.4.14.2`, **pin MetaRocq `9.1` branch** (unreleased), `opam install --deps-only` builds Rocq 9.1, MetaRocq, CompCert, WasmCert etc. "about half an hour on a recent laptop", then `./configure.sh; make -j4; make plugin; make cplugin`; "Building the theories is by far the slowest step" [V: INSTALL.md]. Wasm tests need node 22+ and wabt [V].
- opam deps: `coq >= 9.1 & < 9.2~`, `coq-compcert = 3.17`, `rocq-equations = 1.3.1+9.1`, `rocq-metarocq-erasure-plugin >= 1.5.1`, `rocq-metarocq-safechecker-plugin >= 1.5.1`, `coq-wasm >= 2.2.1`, mathcomp `< 2.6~` [V: `rocq-certirocq.opam`]. WasmCert-Coq 2.2.1 allows Rocq 9.0-9.2 so the two are compatible at Rocq 9.1 [V: both opam files]; PR #166 "Update wasmcert to 2.2.1" merged 2026-10-14 [V].
- CI "Nix CI for bundle default" takes 48-90 min per run [V: Actions API]. No official RAM figure; MetaRocq builds are heavy, I would plan on >= 16 GB [I].

### End-to-end theorem for our decoder (what it would look like)
Write `decode_step : state -> list byte -> state * list N` in Gallina and prove it against the spec in Rocq (agent-friendly, no Wasm reasoning at all). Then compile `main := encode_result (decode_step s0 input0)` for *each concrete test input*, getting only the instance-wise statement "Wasm computes what Gallina computes". There is no universally quantified theorem about the Wasm module because the module is regenerated per closed program [I]. So the final theorem would be about the Gallina function (Rocq), with CertiCoq as a (partly verified) compiler and JS glue as trusted. Distance from spec to code is small in the source language but the *reach* is the lowest of all candidates for a streaming API.

### Smallest existing verified example
The test programs (`demo1`, `list_sum`, `sha256` from a verified Coq implementation) are verified only through the general compiler theorem; there is no per-program proof [V: `tests/wasm/TESTS`, `tests.v`].

### Biggest risk
Interface mismatch (closed programs, no input arguments), unverified glue for all I/O, no GC, heavy and moving toolchain (unreleased MetaRocq pin, `Admitted` in optimisation passes), long builds.

### GC arrays / js-string
Outside the verified path (verified backend does not emit GC; the WasmGC variant is unverified [V: paper]).

### Feasibility: **low** for this experiment (high for "verified Gallina program compiled to Wasm" as a whole different experiment).

---------------------------------------------------------------------------------------------------

## 4. WasmCert-Isabelle and WasmRef-Isabelle

### Links and activity
- https://github.com/WasmCert/WasmCert-Isabelle (master). Last commit **2026-08-27** (merge PR #23); active updates for Isabelle2025-1/2025-2 in Jan-Feb 2026 and Wasm 2.0 update on 2025-08-28 (PR #15) [V: git log]. 39 stars [V: API].
- AFP entry (old 2018 snapshot, Native_Word only): https://www.isa-afp.org/entries/WebAssembly.html; the AFP page lists releases up to Isabelle2026 [V]. Note: the GitHub repo is the live version; the AFP entry is a stale snapshot [I].

### Version and requirements
- README: "you first need Isabelle2025-2 ... together with AFP" [V]. Session `WebAssembly_Dev` with `HOL-Library` + `Native_Word`; ROOT has `options [quick_and_dirty]`; ~27,500 lines of `.thy`; **one `sorry`/`oops`** appears in `Wasm_Instantiation_Properties.thy` [V: grep].
- Wasm 2.0: reference types, bulk memory, new instructions, subtyping for instruction sequences, instantiation changes; SIMD and multi-value earlier. The ICFP/SPLASH WebAssembly Workshop 2025 abstract does not mention GC or multi-memory [V: https://conf.researchr.org/details/icfp-splash-2025/webassembly-ws-2025-papers/9/Updating-WasmCert-Isabelle-to-WebAssembly-2-0]. `Wasm_Ast.thy` has no struct/array [V: grep]. So **no GC**.
- Build/RAM: not documented. [I] ~10-30 min and 4-8 GB for a 27k-line HOL session; install is `isabelle` + AFP link, painless relative to opam.

### What exists
- Type soundness (`Wasm_Soundness.thy`), verified type checker (`Wasm_Checker*`), verified instantiation (`Wasm_Instantiation*`), verified executable interpreter (`Wasm_Interpreter.thy`, `run_step`, `run_iter_sound`), code export to OCaml (`WebAssembly/code/WasmRef_Isa.ocaml`) [V: file tree, README].
- Host: `host_func_apply :: s -> tf -> host_func -> v list -> host_state -> (s x v list) option -> bool` relation in `Wasm_Base_Defs.thy` [V].
- **No binary parser/printer**: README of `code/` says "relies on parsing and numeric operations being implemented externally", embedded in a fork of the OCaml reference interpreter with `-isa` flag [V].
- WasmRef-Isabelle (PLDI 2023: monadic fast interpreter, 2-step refinement, Wasmtime fuzzing oracle): paper https://doi.org/10.1145/3591224 [V: PLDI page]. I could not find a public source repo for the *monadic* interpreter; the interpreter in `WasmCert-Isabelle` is the non-monadic one [V: file list; I for "not public"]. It targets Wasm 1.0 + SIMD [V: workshop abstract].
- Program logic: **Wasm Logic** (Watt, Maksimovic, Krishnaswami, Gardner, ECOOP 2019, https://arxiv.org/abs/1811.03479): separation-logic program logic for first-order *encapsulated* Wasm (single module, no imports/exports/host/`call_indirect`), proved sound in Isabelle/HOL against a big-step semantics (equivalence with small-step mechanised), ~10,400 lines, B-tree library case study [V: abstract; Rao thesis s5.7]. I found **no public repository or artifact link** for the mechanisation and it predates the 2025-26 rewrite [V: Dagstuhl/arXiv pages give none; I for "not usable with the current mechanisation"].
- Examples of verified Wasm programs in the current repo: none [V: tree listing].

### End-to-end theorem for our decoder
Same shape as the Rocq one, via `Wasm.thy` `reduce`/`reduce_trans` (small-step) and `Wasm_Instantiation`; the object is the Wasm AST (`m`), module bytes only via external parser [V/I]. Isabelle's `sledgehammer`, `auto`, and `simp` strongly aid arithmetic/bit-fiddling lemmas on UTF-8 byte ranges [I].

### Biggest risk
Having to invent the Hoare/wp layer *and* work with a 27k-line development whose Wasm 2.0 refactor "touched most of the mechanisation" [V: workshop abstract], with a `sorry` and `quick_and_dirty` in the session; no worked program proofs to imitate.

### GC arrays / js-string
Outside the semantics (no GC).

### Feasibility: **medium-low**. If a later experiment needs an Isabelle entry, the interpreter (executable, verified) is a good oracle for differential tests on concrete inputs [I].

---------------------------------------------------------------------------------------------------

## 5. Lean 4

### 5a. Talos (cajal-technologies) -- the stand-out

- Repo: https://github.com/cajal-technologies/talos. Created **2026-05-20**, last commit **2026-11-02** ("chore: bump toolchain to Lean v4.35.0 (#266)"), 194 stars, 25 open issues, ~28 commits since 2026-09-01 in the shallow history I fetched; authors include Daniel Estevez (23 commits in the window), Marcelo Fornet, others [V: git log/API].
- Description: "WebAssembly interpreter written in Lean 4 ... The same definitions that execute a Wasm program are the ones you reason about", Weakest Precondition calculus; goal "feature-complete executable semantics" [V: README]. Licence **AGPL-3.0** [V].
- Has `AGENTS.md` and `CLAUDE.md`, i.e. is itself developed with coding agents and tuned for them; `docs/std_guide.md`, `verifier/` tooling that builds Rust crates to Wasm, extracts `Program.lean`, and expects hand-written `Spec.lean`/`Proofs.lean` [V].
- Lean toolchain `v4.35.0`, Mathlib `v4.35.0` required by `interpreter/lakefile.toml`; packages in a shared `.lake/packages` [V].

**Completeness** (all [V] from `interpreter/Interpreter/Wasm/` and `IirisMigration.md`):
- `Syntax.lean` 1304 lines, `SmallStep.lean` 8078 lines, `Validate.lean` 1752, `Mem.lean`, `Simd.lean`, `IEEE754.lean`, `Wp/*` (~2600 lines). ~75,000 lines in interpreter + codelib.
- Spec testsuite baseline recorded: **64,740 pass / 0 fail / 357 skip / 18 cascade / 27 decode errors / 0 interpreter errors** (`testsuite_report.txt`).
- Memory (incl. `memory.grow/fill/copy/init`, data segments), globals, tables (`table.grow/fill/copy/init`, `call_indirect`), `loop/block/br_table`, multi-value, exceptions (`try_table`, `throw_ref`), bulk, tail calls (inferred from the file list), **GC: `struct`, `array`, `i31`, `array.new_data/new_elem/init_*`, `any.convert_extern`/`extern.convert_any`, `ref.cast`** (`Value.anyref`, `Store.gcHeap`, `HeapObj.struct/array`) [V].
- Module instantiation: active/passive segments, start function, imports, linking registries, exports (`ExportCall`, `Universal.RunsExport`) [V].
- Host imports: `HostFn.invoke : Store α -> List Value -> HostResult α` with `Return`/`Trap`/`Throw`; `HostSpec`/`HostContract` as relations over (pre-store, args, outcome) so programs are proved "parametric over any host whose behaviour fits the contract" [V: `Host.lean`]. `externref` is an opaque host index; `AnyRef.host` carries internalised host refs [V: `Syntax.lean`].
- Semantics status: authoritative small-step `Step` relation with a proved-sound/complete deterministic executable `stepChecked?`; iris-lean `Language`, `StateInterp`, adequacy implemented; the *legacy big-step fuel interpreter* is being removed (CONTRIBUTING.md still describes a "fuel-bounded big-step interpreter", i.e. docs drift) [V: `IirisMigration.md`, `CONTRIBUTING.md`, AGENTS.md "iris branch" notice]. The `IirisMigration.md` says Iris proofs "provide partial correctness for now"; separate `TerminatesWith`/`PartiallyMeets` notions exist [V].
- Differential testing against V8 (CI workflow `differential.yml`), plus a "Verifier Freshness" job [V: workflows; `IirisMigration.md` mentions a V8/miscast harness].

**Binary handling**: `.wasm` is converted by shelling out to `wasm-tools print`, then parsed by Lean's own WAT parser (`Decoder/Wat.lean`) into the Lean AST; the pinned `wasm-tools` version matters [V: `Runner.lean` header, `verifier/README.md`, `CONTRIBUTING.md`]. So the theorem is about the Lean `Module` AST; bytes are covered only by trusting wasm-tools plus the WAT parser. Because the Node 26 deliverable is the .wasm file, a reproducible pipeline `.wat -> wasm-tools parse -> .wasm` with a CI check `wasm-tools print` ∘ parse = id-on-AST would be needed [I].

**Examples to imitate** (`programs/lean/Project/*`, sizes are my `wc -l` of all `.lean` in the directory) [V]:
- `ByteEcho` 135 lines, `Xor` 142, `TotalVariation` 118, `RustArray` 247, `HexStdio` 605 (hex encode/decode over stdin/stdout with status byte -- the nearest analogue to a byte-stream decoder, spec in `HexDecodeStdio/DecodeSpec.lean`), `GcdStdio` 2262, `SwapElements` 4172, `NumInteger` 6662, `Mergesort` 17,977 lines in 16 files. `HexDecodeStdio` supporting proofs total ~31,000 lines (loop invariants, allocator, memory layout) -- these are compiled-Rust modules at -O0 with allocator, much heavier than a hand-written WAT.
- Spec style: `∀ input, ∃ output, Runs "export" (args input) (result output) ∧ output = ...` with reference Lean functions (`decode : List UInt8 -> Option (List UInt8)`) -- very close to our LAWS style (relational, existentials) [V: `Project/ByteEcho/Spec.lean`, `HexDecodeStdio/DecodeSpec.lean`]. Explicit OOM host function `talos.oom` for allocation failure [V].
- Handwritten WAT examples in `interpreter/Interpreter/Wasm/Examples/` (~50 files: `MemFill`, `MemCopy`, `MemReplace`, `SimpleLoop`, `SumI64`, `Factorial`, `MeasureLoopDemo`, `HostDispatch`, `UniversalHost`, `RefCastFuncType`) mostly concrete-input; `Wp/Loop.lean` (193 lines) provides a loop rule [V].
- Iris-lean WP contracts and adequacy proofs for handwritten byte/word kernels (swap, partition, merge, fill, overlapping copy with memmove semantics), including `i64.load/store` physical/ghost memory agreement [V: `IirisMigration.md`].

**Install** [V: README/CONTRIBUTING; times [I] unless noted]:
`elan` (Lean toolchain fetched from `lean-toolchain`), `just`, `wasm-tools` (`cargo install wasm-tools --version <pinned>`), then `just lake-shared` and `lake build` per package; `use-mathlib-cache: true` in CI. CI "CI" workflow runs 106-130 min on GitHub macOS runners [V: Actions API]; a developer with Mathlib cache can build just `interpreter` and `codelib` and a single program package in a much shorter time [I]. RAM: Lean elaboration of `SmallStep.lean` (8k lines) and large `decide +kernel` proofs suggests 8-16 GB [I].

**End-to-end theorem for our decoder** (shape, following Talos conventions):
```
def DecodeSpec : Prop :=
  ∀ (st : AbstractState) (buf : List UInt8) ...,
    ∃ out st', Runs "decode_chunk" (args st buf) (result out st') ∧ Utf8.Decode st buf out st'
```
over the instantiated `Module` AST with the Talos small-step semantics (core Wasm 3.0-ish features), parametric in the host contract, i.e. the reach is "Wasm syntax tree under a mechanised (but not spec-generated) Wasm semantics, tested against the official testsuite and V8". Streaming state can be kept in linear memory or globals; `Runs` can be iterated over several exports/calls (`Universal.RunsExport` with host state) [I: depends on whether multi-call sequences with persistent store are supported; Talos has `ExportCall`/`ExportReturn` carrying `final` machine store, so chaining looks feasible but I did not see an example [open question]].

**GC arrays and `wasm:js-string`**: *Statable*. `array` heap objects with `i16` elements live in `Store.gcHeap`; an import such as `wasm:js-string.fromCharCodeArray` can be modelled as a `HostFn` that reads `gcHeap` and returns an opaque `externref` index, with a host-state map from index to the string; `HostContract` can then say "result is a fresh handle whose string equals the UTF-16 code units in [start,end)". No built-in model of `wasm:js-string` exists (grep for `js-string|fromCharCode` finds nothing) [V]; also, the engine-side builtin "imports are the builtin" semantics (type-checking against builtin signatures, `compile with builtins`) must be restated manually [I].

**Biggest risk**: youth and churn (5.5 months old, mid-way through a large semantics rewrite to small-step/iris-lean; theorem shapes in examples "need not retain their exact shape"), docs partly stale, AGPL, Mathlib-sized dependency, and the trusted `wasm-tools`+WAT-parser step between bytes and theorem. Mitigation: pin a commit; in LAWS/PROOF avoid depending on internals beyond `Runs`/WP API [I].

**Feasibility for an agent-driven attempt: high** (agent-oriented repo, many examples with the same spec style, Lean tactic automation such as `omega`, `simp`, `decide +kernel`, `bv_decide`; Lean agents are strong in 2026) [I for the last parenthesis].

### 5b. lean-wasm / WasmLean (T-Brick)
- https://github.com/T-Brick/lean-wasm, created 2023-07-28, last commit **2026-11-02** ("bump to v4.35.0"), Lean 4.35.0, 34 stars, ~7,000 lines of Lean [V: clone/API].
- README: syntax, validation, dynamics, **binary** and **text** modules (directory layout mirrors the spec); "Currently only WASM (binary files) can be converted into WAT"; vectors not implemented; float instructions represented but not implemented; type-checker unchecked; intended as the target of the C0 compiler `c0deine`, which says no compiler phase is proven correct [V: README, search snippet of c0deine].
- No program proofs [V: none present]. Value for us: a **Lean-native binary decoder** written to mirror the spec; could in principle close the byte gap in Talos [I, speculative: ASTs differ, would need a bridging theorem].
- Feasibility as the main vehicle: **low** (no proofs, incomplete). GC: not covered [I].

### 5c. Others in Lean
- LeanWasm: Utrecht thesis, an intrinsically-typed interpreter for Wasm following the reference interpreter [V: https://studenttheses.uu.nl/handle/20.500.12932/46861 as listed in search results; not opened]. Not a program-verification vehicle [I].
- Wasm SpecTec -> Lean: only a forward-looking sentence in a thesis ("SpecTec is soon expected to also output mechanisations in ... Rocq, Agda and Lean") [V: search result]. Nothing found.

---------------------------------------------------------------------------------------------------

## 6. Anything else

### 6a. SpecTec-generated mechanisations
- SpecTec adopted as the official authoring tool; Wasm 3.0 spec is produced with it [V: https://webassembly.org/news/2025-03-27-spectec/; Rao thesis context].
- Announcement text: SpecTec can "generate definitions representing the Wasm semantics in Coq/Rocq"; "started porting the proofs from the hand-written WasmCert mechanization"; "can already handle soundness for the Wasm 1.0 subset"; "Scaling to the full language is work in progress" [V: same page]. Says nothing on Isabelle or Lean.
- `WebAssembly/spec` main (2026-11-10): `spectec/src` has backends `ast, interpreter, latex, prose, splice` -- **no Rocq/Isabelle/Lean backend in the tree** [V: directory listing]. The spectec README still says Coq/Isabelle definitions are a goal ("ongoing work") [V: `spectec/README.md`, `doc/Overview.md`]. A personal gist (raymyers) describes a `rocq-backend` branch emitting a ~13.8k-line `wasm3.v` with `Admitted` decidable-equality lemmas and an `Axiom`; no semantic theorems; branch location not given [V: https://gist.github.com/raymyers/cb693117addd173fc2917463b25a0a2b, first 100k chars read].
- Imperial's group page claims the Rocq translation "has then been used to prove the type soundness of Wasm 1.0 and 2.0" [V: https://vtss.doc.ic.ac.uk/research/webassembly.html] (a claim on a project page, not a released artifact I could inspect).
- Conclusion [I]: not usable as of today; would be the only route to GC-capable *spec-derived* Wasm 3.0 semantics in Rocq, so it should be re-checked in a few months. There is no existing program logic for it.

### 6b. KWasm (K framework)
- https://github.com/runtimeverification/wasm-semantics: last commit **2026-07-30** ("Implement zero-dependency Wasm binary parser (#754)"), described by README as "mature and production-ready semantics ... since 2019"; proofs via `./kwasm prove` using the K Haskell backend + Z3 4.8.15 (pinned) [V: README, API].
- Version supported is not stated in the README; historically Wasm 1.0 [I]. No GC [I].
- Proof style: symbolic execution with reachability claims and loop circularities, SMT-discharged; examples `simple-arithmetic-spec.k`, `wrc20-spec.k` [V: README]. Results are produced by the K prover, **not** by a small proof-assistant kernel (trusted base is the K tooling and Kore backend) [I].
- Feasibility: **low** for our setting (needs Haskell stack, K, Z3 4.8.15 pin; existentials/uniqueness specs over lists are awkward in matching logic claims) [I].

### 6c. CakeML / Pancake / HOL4 -> Wasm
Searches found **no** WebAssembly backend for CakeML or Pancake and no Wasm semantics in HOL4 [V: negative web search results; absence of evidence, not proof].

### 6d. Other verified compilers to Wasm
- CertiCoq-Wasm (section 3) is the only verified Coq/Rocq-to-Wasm compiler per the CPP'25 paper ("to the best of our knowledge ... the only verified compiler from Coq to WebAssembly") [V: paper s5]. Related tool `AU-COBRA/lambda-box-extraction` emits Wasm/C/Rust/OCaml/Elm and uses the verified LambdaBox pipeline [V: search snippet, not opened].
- F*/KaRaMeL (Low* -> Wasm) exists but I found no evidence of a verified translation; not examined [open question].
- Lean's own Wasm output (Emscripten) and `T-Brick/lean2wasm` are unverified experiments [V: search snippet].
- Rust -> Wasm with the theorem on the Wasm: Talos (5a) takes this route.

### 6e. Other program logics on Wasm
- Iris-WasmFX (PLDI 2026) [I: see section 1], MSWasm, RichWasm built on Iris-Wasm [V: iriswasm page via search snippet]. All are Iris/Rocq on 1.0-era base.
- "CHC-based Automated Verification of WebAssembly Programs" (arXiv 2607.17220, Jul 2026): automated static CHC solver approach for a Wasm subset; no named tool, no proof assistant [V: arXiv abstract page]. Trust base is the solver; not applicable.

### Verified runtimes
None found that would extend reach to a runtime executing the module. The verified interpreters (WasmCert-Coq extraction, WasmRef-Isabelle) are *reference interpreters for the same semantics*, not production runtimes: they could serve as oracles in differential tests against Node 26, as WasmRef-Isabelle serves for Wasmtime fuzzing [V: PLDI'23 abstract], and Talos does against V8 [V]. Nothing proves V8/Node correct.

---------------------------------------------------------------------------------------------------

## 7. js-string builtins summary

| Mechanisation | Can it type/state a module importing `wasm:js-string` `fromCharCodeArray`? |
|---|---|
| Talos | Yes in principle: GC arrays + host functions over the full store; the builtin must be modelled by the user as a `HostFn`/`HostContract` and strings as opaque host refs [V components; I for the conclusion] |
| WasmCert-Coq | No (no GC types) [V] |
| Iris-Wasm | No (1.0) [V] |
| WasmCert-Isabelle | No (no GC) [V] |
| CertiCoq-Wasm | No (verified path emits no GC) [V] |
| lean-wasm, KWasm | No/unknown [I] |
| SpecTec-Rocq | Would include GC in 3.0, but not available [I] |

A linear-memory-only decoder interface (JS writes bytes into memory, reads UTF-8/UTF-16 out) avoids the issue in every mechanisation [I].

---------------------------------------------------------------------------------------------------

## 8. Per-candidate quick card

| Candidate | Last commit | Versions | Install | Build time / RAM | Smallest verified example | Biggest risk | Feasibility |
|---|---|---|---|---|---|---|---|
| Talos | 2026-11-02 | Lean 4.35.0, Mathlib 4.35.0 | elan, just, wasm-tools, `lake build` | CI 106-130 min (macOS, cached Mathlib); RAM [I] 8-16 GB | `Project/ByteEcho` 135 lines; `HexStdio` 605 | young + rewriting semantics; trusted wasm-tools/WAT step; AGPL | **High** |
| WasmCert-Coq | 2026-10-12 | Rocq 9.0-9.2, mathcomp 2.4-2.6, CompCert >=3.14, wasm=2.0.2 | `opam install coq-wasm` / `opam install .` | CI 11-14 min; README >= 8 GB | none (only interpreter conformance) | no program logic, no GC | Medium |
| Iris-Wasm | 2025-01-30 | Coq >=8.20.1, Iris >=4.3.0, Wasm 1.0 | `opam install .`, OCaml 4.14.2 | README >30 min, >= 8 GB | `iris_examples.v` 378 lines; stack module ~200 LOC / ~2100 LOC proofs | stale, may not build on Rocq 9; 1.0 only | Low-Medium |
| WasmCert-Isabelle | 2026-08-27 | Isabelle2025-2 + AFP | Isabelle + AFP link | [I] 10-30 min, 4-8 GB | none | no logic; `sorry`; quick_and_dirty | Medium-Low |
| CertiCoq-Wasm | 2026-11-03 | Rocq 9.1, MetaRocq 9.1 branch, CompCert 3.17, coq-wasm >=2.2.1, OCaml 4.14.2 | from-source, `INSTALL.md` | deps ~30 min + theories "slowest"; CI 48-90 min; RAM [I] >=16 GB | no per-program proofs | closed programs; unverified I/O glue; no GC; Admitted passes | Low |
| lean-wasm | 2026-11-02 | Lean 4.35.0 | `lake build` | [I] minutes | none | incomplete semantics | Low |
| KWasm | 2026-07-30 | K, Z3 4.8.15 | K toolchain | [I] long | `wrc20-spec.k` | prover trust base, agent-unfriendly | Low |
| SpecTec->Rocq | n/a | n/a | n/a | n/a | n/a | not published | n/a |

---------------------------------------------------------------------------------------------------

## 9. Ranking (for an agent-driven attempt at a verified Wasm streaming UTF-8 decoder)

1. **Talos (Lean 4).** Only candidate with an *already usable* program-reasoning layer, GC arrays, imported host functions with contracts, a large conformance score, memory-loop and byte-stream examples with relational specs close to our LAWS, and an agent-oriented repo. Weakest points: youth/churn, trusted `wasm-tools`+WAT parser between the shipped `.wasm` and the theorem, AGPL, Lean/Mathlib build size.
2. **WasmCert-Coq (Rocq), proofs done directly against `reduce`, with Iris-Wasm rules as a template.** Most mature and spec-conformant (2.0), solid toolchain on Rocq 9.x, extracted verified interpreter usable as a differential oracle; but no 2.0 program logic, no GC, unverified binary parser, and agents must build the Hoare layer.
3. **Iris-Wasm (Rocq, Wasm 1.0).** Real program logic and examples, but stale (Jan 2025), 1.0-only, uncertain build on Rocq 9, large ownership-reasoning overhead.
4. **WasmCert-Isabelle.** Good prover and verified interpreter, Wasm 2.0, but nothing to reason about specific modules, a `sorry`, no GC, no public program logic.
5. **CertiCoq-Wasm.** Strongest "reach" story for *compiled Gallina*, but wrong shape (closed `main`, no input channel, no GC, unverified glue, incomplete source-to-ANF chain, heaviest toolchain).
6. lean-wasm; 7. KWasm; SpecTec backends: not viable now.

Suggested de-risking step before committing (not done here, since this task was read-only) [I]: spend one agent-session on each of the top two with a throwaway task -- "prove a hand-written WAT loop that sums N bytes from memory, for all N and memory contents" -- and compare time to green.

---------------------------------------------------------------------------------------------------

## 10. Open questions / things I could not establish

- Whether Iris-Wasm builds against Rocq 9.x / current Iris, and whether Iris-WasmFX (https://github.com/logsem/iris-wasmfx) is based on WasmCert-Coq 2.x or on the 1.0 fork (ACM page returned 403; only search snippets).
- Talos: whether multi-call sequences with persisted store/state across several exports have an existing `Runs`-chaining combinator (needed for the "any split into buffers" law); build time/RAM on a fresh Linux box (CI numbers are macOS and include everything); stability promise of the WP/iris-lean API; git history before 2026-08-31 (shallow clone).
- CertiCoq-Wasm: exact reconciliation of the OOM disjunct in the paper theorem versus the stated Rocq theorem (`toplevel_theorem.v` conclusion has no explicit disjunct); RAM numbers; whether PR #183 (export table) could give a verified calling interface for exported functions.
- WasmCert-Isabelle: build time/RAM; whether a non-public copy of the 2019 Wasm Logic mechanisation exists; whether the monadic WasmRef-Isabelle (PLDI'23) source is published.
- SpecTec Rocq backend: location/status of the `rocq-backend` branch and any Wasm 3.0 (GC) preservation/progress proofs.
- The text of the CertiCoq-Wasm paper was recovered by naive PDF text extraction (some ligatures lost); quotations are therefore paraphrased or lightly normalised.
- Rao thesis was read only through naive text extraction; numbers (LOC table, 200/2100 lines) are from that extraction.
