# Verified UTF-8 decoder in WebAssembly: comparison of three toolchains

Written 2026-11-12, at the end of the second session (EC2, m8i.2xlarge:
Xeon 6975P-C, 8 vCPU, 30 GB). `HANDOVER.md` describes the experiment and the
state after the first session; this file supersedes its sections 6 and 7.

All three candidates now have a proved top-level theorem, a machine-checked
non-vacuity theorem, an independent audit, an improvement pass, and a
re-audit of the improved proofs. Every claim below is from those audits and
from uncontended measurements unless marked otherwise.

## 1. What each candidate proves

| | Aeneas | Talos | WasmCert-Coq |
|---|---|---|---|
| Prover | Lean 4.36.0-rc2 | Lean 4.35.0 | Rocq 9.2.0 |
| Decoder written in | Rust (115 lines) | Wasm text, by hand | Wasm, as a Rocq term |
| The theorem is about | The Lean model Aeneas generates from the Rust | The Wasm module Talos decodes from the text `wasm-tools print` gives for the shipped bytes | The Wasm module as a Rocq term; the shipped bytes are proved to be the printer's output and to parse back to it |
| Wasm semantics used | none | Talos (created May 2026, work in progress, tested against the spec suite and V8) | WasmCert-Coq 2.2.1 (established mechanisation of Wasm 2.0, with a verified interpreter) |
| Instantiation | not applicable | not modelled; validation outside the theorem | proved, including module typing; proved to have exactly one result |
| "Returns" means | the model function returns a value | terminates without trapping (Talos proves its step relation deterministic) | the result is the only outcome: reachable, no trap or other result reachable, no infinite run (determinism proved here, see section 5) |
| Axioms | Lean's three standard | Lean's three standard | nine from the library: classical logic, functional extensionality, two real-number axioms, five opaque SIMD functions |
| Audit verdict | holds | holds | holds, after a critical defect was found and fixed (section 4) |

Trusted and outside every theorem: the JS wrapper (35 to 52 lines), the
JS–Wasm calling convention, and V8.

Additionally trusted, per candidate:

- **Aeneas:** Charon and Aeneas (the translation is not mechanically
  verified), rustc and LLVM's Wasm backend (and that the release build
  behaves as the translated code), a small unsafe Rust shim that turns raw
  pointers into slices. Nothing in the theorem mentions Wasm.
- **Talos:** `wasm-tools print`, Talos's text parser, Talos's semantics (not
  proved against the Wasm specification), instantiation. The user's decision:
  use Talos as it is and state this as the limit of its proof reach.
- **WasmCert-Coq:** that the mechanised semantics matches what V8 does, that
  V8 decodes the bytes as the library's (unverified) parser does, and
  `TextDecoder('utf-16le')`, which turns the module's UTF-16 output into a
  string.

## 2. The four criteria

### a. Simplicity

| | Aeneas | Talos | WasmCert-Coq |
|---|---|---|---|
| Layers between spec and running code | Rust → Charon → Aeneas → Lean; Rust → rustc → Wasm | Wasm text → bytes → printed text → Talos module | Rocq term → bytes |
| Statement files (lines) | 169 | 257 | 352 |
| Candidate-specific proofs | 385 | 958 | 1,679 |
| Infrastructure that had to be written | 0 | 192 (symbolic-execution tactic) | 2,071 (symbolic execution 761, determinism 1,310) |
| Shared pure layer | 1,148 | 1,148 | 1,045 |
| Shipped module | 5,487 bytes | 880 bytes | 643 bytes |
| Setup on a fresh machine | 2.5 min | 2.5 min with a prebuilt checkout (20 min from scratch on the old VM) | 10 min |

Neither Wasm-level system had a usable program logic. Talos ships one, but
on its old semantics and needing Mathlib; WasmCert-Coq 2.2.1 has none. Both
agents wrote their own.

The boundary file grows as the theorem gets closer to the bytes, because
more has to be defined in it: Aeneas's talks about slices and counts;
WasmCert-Coq's defines memory layout, how values are encoded, what a call
is, and what "only outcome" means.

### b. Proof reach

Ordered from furthest to nearest: WasmCert-Coq (Wasm syntax tree, tied to
the exact bytes by a proved round trip, with instantiation and typing),
Talos (Wasm syntax tree, via two trusted tools), Aeneas (a model of the
source program).

None reaches a runtime, and none has a verified binary parser.

### c. Difficulty for coding agents

Agent time, Opus, on this machine and the first session's VM:

| | Aeneas | Talos | WasmCert-Coq |
|---|---|---|---|
| To a proved top-level theorem | 20 min | 57 min (42 + 15) | 1 h 38 min (45 + 47 + 6) |
| Determinism (needed only here) | — | — | 49 min, plus 14 min to wire in |
| Fixing the vacuous statement | — | — | 28 min |
| Non-vacuity theorem | 10 min | 15 min | part of the fix |
| Improvement pass | 23 min | 29 min | 34 min |
| Total | about 55 min | about 1 h 50 min | about 3 h 45 min |

Shared pure layers took another 74 min (Lean) and 100 min (Rocq),
including their improvement passes.

What the journals show:

- **Nobody got stuck on semantics.** Every recorded difficulty was tooling:
  ssreflect goal order, `lia` on large literals, Lean macro hygiene, a
  profiler that misattributed time.
- **Agents' own estimates were far too high.** Talos: estimated 1.5 to
  2.5 hours to finish, took 15 minutes. WasmCert-Coq `step_spec`: estimated
  3 to 6 hours, took 53 minutes. Determinism: described as a multi-week item
  for human authors, took 49 minutes.
- **Aeneas shaped the Rust.** Compound `&&`/`||` conditions translate to
  large nested Lean, so they live in one-boolean helper functions. The
  improvement pass re-tested this and kept them.
- **Sensitivity to code edits.** Aeneas: small edits need no or small proof
  edits. Talos, after its improvement pass: operand swaps and reordering
  need none in the step function; loop code still does. WasmCert-Coq: the
  proofs follow the instruction sequence, so any edit needs proof edits.
- **The one real defect was in a statement, not a proof** (section 4).

### d. Check time

Reference: `bend PROOF.bend` takes 1.8 s here.

Proof checking alone (uncontended):

| | Aeneas | Talos | WasmCert-Coq |
|---|---|---|---|
| Shared layers | 5.8 s | 6.0 s | 38.7 s (pure layer, symbolic execution, determinism) |
| Candidate's own files | 6.6 s | 28.8 s, of which about 22 s is Talos decoding the module text in the kernel | 29.3 s |
| Total | about 12 s | about 35 s | about 68 s |

Full default check, including the differential harness (about 30 s) and an
independent re-check of the compiled proofs:

| | Aeneas | Talos | WasmCert-Coq |
|---|---|---|---|
| Wall time | about 2 min 14 s | 2 min 43 s | about 2 min 5 s |
| Peak memory | 6.7 GB | 7.1 GB | 1.0 GB |
| Independent re-check | Lean kernel replay, 81 s | Lean kernel replay, 125 s | `rocqchk` on project files, 12 s (60 s including installed libraries) |

The Aeneas and WasmCert-Coq full-check figures were measured while another
agent was running and should be re-measured; the others are uncontended.

The Lean kernel replay is not optional: the Talos re-audit built a false
theorem through metaprogramming that passed the build, the statement pins
and the axiom check, and only the replay rejected it.

Effect of the improvement passes (first attempt → skilled use):

| | Before | After |
|---|---|---|
| Rocq pure layer | 8 min 40 s | 22 s |
| Lean pure layer (two Lean versions) | 1 min 55 s | 12 s |
| Talos own proofs (CPU) | 93.7 s | 34.4 s |
| WasmCert-Coq decoder and reusable files (CPU) | 63.1 s | 16.7 s |
| Aeneas own proofs (CPU) | 11.2 s | 9.8 s |

In every case the cause was how the proof was written (brute-force
enumeration, `omega` given whole tables, a quadratic tactic driver, `simpl`
evaluating literals), not the system.

## 3. What a second verified module would reuse

- **WasmCert-Coq:** the symbolic-execution library and the determinism
  library (2,071 lines), which cover integer code on a fixed linear memory
  with no imports. Determinism is proved for a syntactic fragment and
  applies unchanged to any module inside it.
- **Talos:** the 192-line tactic file.
- **Aeneas:** nothing needed to be written.
- **All:** the pattern of spec, pure layer with a reference decoder,
  boundary file, non-vacuity theorem, and check script.

## 4. Lessons about the method

1. **A proved theorem can be vacuous.** WasmCert-Coq's boundary file
   required 327,684 bytes of memory; the module has 327,680. Every per-call
   guarantee was conditional on something false of the real module. The
   proof was genuine, all mutation tests passed, and three authoring
   sessions missed it. An auditor found it by reading. All three candidates
   now carry a non-vacuity theorem, and their check scripts tie the
   wrapper's layout constants to the boundary file.
2. **Independent audits earned their cost.** Each took 15 to 35 minutes.
   Besides the vacuity defect they found: check scripts that passed with a
   broken boundary file, a comparison that could never fail, a build that
   hung instead of failing, and a statement that would have been trivially
   true if the module failed to decode.
3. **Mutation tests have a blind spot.** They show that changing the code
   breaks the proof. They cannot show that the statement's hypotheses are
   satisfiable, and for proofs that follow the code instruction by
   instruction they show little about which argument does the work.
4. **Check scripts need the same scrutiny as proofs.** The verdict line is
   what a non-reader of proofs relies on.
5. **The spec's 32-boolean code point.** In Rocq it caused the 509 s
   enumeration (first attempt) and three kernel hangs at the end of proofs,
   fixed by making one definition opaque at the end of the pure layer. It is
   a trap to seal off, not a pervasive cost. Evidence for the later
   idiomatic rewrite of the specs.

## 5. Determinism in WasmCert-Coq

WasmCert-Coq states execution as a relation and version 2.2.1 has no
determinism theorem, so "the call reduces to this result" did not exclude a
trap. `candidates/wasmcert-coq/determinism/` proves one-step determinism for
a fragment (integer arithmetic, locals, globals, integer loads and stores,
blocks, loops, branches, calls to module-defined functions; no host calls),
with no typing hypothesis, and the corollary that a call's result is its
only outcome. Not yet covered though deterministic in this mechanisation:
`call_indirect` and tables, floats, SIMD, `memory.grow`, bulk memory.

## 6. Still by reading in all three

- That the wrapper passes back only states the module returned, uses its
  constants as the boundary file assumes, and does not grow memory.
- The induction from "one call preserves the conditions" to "any sequence
  of calls".

## 7. Open items

- Re-measure the Aeneas and WasmCert-Coq full checks uncontended.
- Talos's kernel replay does not recompute the axiom list on the replayed
  environment (the Aeneas one now does).
- The Aeneas library declares unused `bv_decide` native axioms; they are not
  in the theorems' axiom lists.
- Talos: two smaller proof files still use the old tactic.
- Aeneas throughput is low (ASCII 37 MB/s against 1,563 MB/s for
  `TextDecoder` on the old VM), probably the wrapper's conversion; not
  profiled. The other two were not measured.
- Idiomatic rewrites of the specs, when the user asks.
- `wasm:js-string`: only Talos can state a module that uses it, against a
  hand-written trusted model of the builtin. Not pursued.

## 8. Where things are

| Path | What |
|---|---|
| `candidates/<name>/decoder/STATUS.txt`, `REPORT.txt`, `AUDIT.txt`, `IMPROVEMENT.txt` | Per-candidate state, audit and re-audits, improvement record |
| `candidates/<name>/decoder/check.sh` | The check; read its verdict line, not its exit code |
| `candidates/*/decoder/Boundary.*` (Aeneas: `lean/Boundary.lean`) | The claim |
| `candidates/pure-lean/`, `candidates/pure-rocq/` | Shared pure layers |
| `candidates/wasmcert-coq/symexec/`, `determinism/` | Reusable Rocq libraries |
| `candidates/BASELINE-EC2.txt`, `AFTER-PASS1-EC2.txt`, `FINAL-EC2.txt` | Measurements |
| `candidates/CHECK-SCRIPTS-AUDIT.txt` | Check-script findings and fixes |
