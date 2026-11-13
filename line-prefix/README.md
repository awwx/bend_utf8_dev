# Verified streaming line prefixes

This demo uses a hand-written WebAssembly module to prefix every LF-delimited
line with `> ` through Node streams. Empty input stays empty; trailing LF adds
no final prefix. CR is ordinary text. The independent specification and scope
are in [FRAMING.md](FRAMING.md), and the bridge assumptions are in
[CONTRACTS.md](CONTRACTS.md).

## Run

```sh
node line-prefix/bridge.mjs input.txt output.txt
```

Use a fixed valid UTF-8 input and a separate output file. The command resolves
after the output finishes. It reports runtime errors, but error recovery is
outside the proof. Backpressure is ignored: the host output queue can grow
without a fixed bound.

Wasm creates streams and registers callbacks through imports, remembers
whether the next character begins a line, transforms incoming chunks, queues
writes, and requests output closing. The bridge handles Node API adaptation
and encoding conversion; it contains no line-prefix algorithm.

Each Node `data` event is forwarded unchanged through `data(text)`. Wasm
obtains the string length, chooses slices of at most 4096 UTF-16 code units,
and keeps surrogate pairs together. It calls native `intoCharCodeArray` and
`fromCharCodeArray` around the existing GC-array transformation. Each internal
slice produces one immutable output string; an empty delivery produces none.
The bridge contains no text loop, length argument, chunk-size configuration,
or surrogate checks.

The module's `_chunk` export is a proof entry for the bounded helper; the
bridge calls only the public `data` callback. Every Node string fitting the
native unsigned-i32 length interface is covered, without a whole-file limit
or cumulative i32 file counter. No linear memory is used.

## Build and verify

Use the existing Talos environment described in
[the setup notes](../candidates/talos/SETUP.md). The pinned dependencies are
Lean 4.35.0, Talos commit `d7c84ac660757953b752bdfc9cb8dae3dab623ed`, and
wasm-tools 1.251.0. Runtime tests use Node 26.13.0 with native `js-string` builtin support.

```sh
./line-prefix/build.sh   # Rebuild the shipped bytes and canonical WAT.
./line-prefix/check.sh   # Fresh proof build, axiom audit, kernel replay, runtime tests.
```

The checker rejects a changed Talos checkout, stale imported Talos builds,
proof holes and unexpected axioms. It compiles local sources in a fresh
temporary directory. Independent replay rechecks every imported non-core
constant in a fresh Lean kernel environment. `--skip-replay` is available
for iteration and explicitly reports the omitted check. The final acceptance
run must include replay.

The runtime tests include empty input, final and consecutive LFs, CRLF,
supplementary characters, byte splits inside UTF-8 sequences, all raw
partitions of a small Unicode input, chunk boundaries after LF, worst-case
output capacity, delayed write completion and immutable string capture, every
Unicode scalar, and real-file I/O. They also check that the engine supplies
all five native builtin imports and the module exports no linear memory. Tests check the trusted runtime boundary; they are
not substitutes for the universal proofs.

Full verification passed on the m8i.2xlarge in 2 minutes 56 seconds, with
approximately 6.9 GiB peak process RSS. Independent kernel replay checked
12,838 non-core declarations, and all ten audited results use only Lean's
standard axioms. Runtime checks passed 123 stream cases, every Unicode scalar,
real-file byte-split I/O, and direct empty/large full-string callback tests.

## Specification and proof organization

- `TextSpec.lean`: independent predecessor-based `prefixLines`, scalar validity,
  chunk composition and UTF-8 output properties. Reuses the accepted UTF-8
  laws and checked decoder facts from the earlier developments.
- `Utf16.lean`: scalar/UTF-16 representation, surrogate bounds, decoding
  roundtrip, and correctness of processing UTF-16 units.
- `Chunking.lean`: the concrete surrogate-boundary test, termination, complete
  character slices, and preservation of the full input.
- `OuterModel.lean`: the sequence of writes and state changes across internal slices.
- `GcSupport.lean`: GC heap lookup/update and fixed-capacity output array facts.
- `WasmGcHosts.lean`: builtin conversion and string-write invocation proofs.
- `WasmGcEntry.lean` and `WasmGcExit.lean`: allocation, input conversion,
  output conversion, and queueing at the callback boundaries.
- `WasmModule.lean`: the exact module decoded from canonical WAT.
- `Wasm.lean`: individual host operations, initialization and close callbacks.
- `WasmLoop.lean` and `WasmCallback.lean`: actual Talos execution of the data
  callback and its loop, including array access and host argument bounds.
- `WasmOuter.lean`, `WasmOuterCall.lean`, and `WasmOuterProof.lean`: actual
  public-callback execution,
  including builtin string access and internal helper calls.
- `Execution.lean`: stream queues, asynchronous completion, progress, universal
  completed-output correctness and a concrete eager execution witness.
- `WasmExecution.lean`: refinement using persistent Talos stores, GC heaps, immutable
  host strings, and actual callback execution, connecting the module to the stream theorem.
- `Proof.lean`: the final claims, discharging the callback proof obligations
  for the shipped module. `Audit.lean` checks their types and axioms.

The reviewable final claims are `PrefixWasm.ShippedCorrect` and
`PrefixWasm.ShippedExecutionsExist` in [WasmExecution.lean](WasmExecution.lean).
[Proof.lean](Proof.lean) proves both for the shipped module. Correctness covers
initialization, terminating callbacks with no alternative trapped outcome,
complete-scalar writes to the right output, and every permitted fair execution:
it eventually finishes, and every finished state contains exactly
`encodeUtf8(prefixLines(decodeUtf8(input)))`, which is valid UTF-8. Existence
constructs a faithful abstract delivery for every valid input and raw partition,
and an initialized fair execution for **every** allowed delivery, including
the unchanged strings supplied by Node.

## Artifact and trust boundary

The theorem's module is the Talos AST decoded from `prefix.printed.wat`.
The decoder result is checked by a Lean theorem, rather than trusting the
elaborator that constructs the AST. The checker verifies that `prefix.wasm`
is exactly a rebuild of `prefix.wat`, validates those bytes, and checks that
printing them yields the exact text used in the theorem.

This connection trusts wasm-tools parsing, printing, stripping and validation;
it is not a verified binary parser or compiler theorem. The runtime Wasm
engine must agree with the pinned Talos semantics, including instance
initialization. Node and the bridge must implement the individual contracts
in `CONTRACTS.md`. JavaScript source itself is not formally verified.

The string builtins have explicit formal host models; their implementations
in Node/V8 remain trusted. The bridge enables them through Wasm compilation
options and supplies no JavaScript conversion polyfills. GC is modeled as
abstract allocation without reclamation. The proof does not establish timing,
throughput, bounded host memory, collection latency, or security noninterference.
