# Proving a streaming line-prefix program in WebAssembly

This project is a formal verification demo of a WebAssembly program that
reads a valid UTF-8 file through Node, obtains and manipulates text, and
writes a UTF-8 file with each input line prefixed by `> `.

We will use Lean and Talos's WebAssembly semantics. A JavaScript bridge
connects the module to Node's streams and event loop. Initially, we assume
that the bridge implements its specified contracts correctly; the focus
is correctness of the program executing on the WebAssembly side.

This document frames the work. It does not claim that the program, bridge,
or proofs have been implemented. The existing [copier demo](../copier/README.md)
and [candidate developments](../candidates/COMPARISON.md) provide prior work
to inspect and reuse, not proofs of this new program.

## Required text transformation

The specification is over a finite sequence of Unicode scalar values,
independently of input buffers, callbacks, memory layouts, or implementation
state. Newline means exactly U+000A (LF). The prefix consists of U+003E
(`>`) followed by U+0020 (space).

For each character of the input, in order, emit the prefix immediately
before that character if it is the first character or its predecessor is
LF. Emit the original character unchanged. Emit nothing else.

Equivalently, for text `T` of length `n`, concatenate, for each index
`0 ≤ i < n`, the prefix when `i = 0` or `T[i-1] = LF`, followed by `T[i]`.
Call this whole-text function `prefixLines(T)`.

This definition gives the following examples; escapes denote characters,
not literal backslashes:

| Input | Output |
|---|---|
| `""` | `""` |
| `"hello"` | `"> hello"` |
| `"hello\n"` | `"> hello\n"` |
| `"hello\nworld"` | `"> hello\n> world"` |
| `"\n"` | `"> \n"` |
| `"\n\n"` | `"> \n> \n"` |
| `"a\n\nb"` | `"> a\n> \n> b"` |
| `"a\r\nb"` | `"> a\r\n> b"` |

In particular, empty input produces empty output. Every nonempty input
starts with a prefix, including input beginning with LF. A trailing LF
does not produce an additional prefix. CR and all other characters are
ordinary text; there is no newline normalization, Unicode normalization,
or other transformation.

## Program and bridge responsibilities

The WebAssembly program controls the application: through bridge imports
it constructs an encoded input stream and a UTF-8 output stream, registers
the data and close callbacks, transforms incoming text, queues output,
and requests output closing. State needed across callbacks belongs to the
Wasm program. The JavaScript bridge handles API adaptation and event
delivery; it must not implement the line-prefix transformation.

There is one copier instance. Callbacks into Wasm run serially, without
reentrant entry during an imported call. Initialization completes and
listeners are registered before delivery begins. Normal input close is
delivered only after all decoded text, including decoder finalization.
The input close callback requests output closure; it is not itself output
completion.

The precise module interface and text representation are implementation
choices. UTF-16 code units are a natural option because Node supplies
JavaScript strings. The bridge may use WasmGC arrays, linear memory, or
appropriate string builtins such as `intoCharCodeArray` and
`fromCharCodeArray`. Their names do not imply that Talos already supplies
their semantics: any builtin used needs an explicit model or contract.

The representation must have a precise mathematical relation to Unicode
text. If UTF-16 is used, account for surrogate pairs and prove that the
program's transformation agrees with the scalar-level specification.
Do not silently equate a code unit with a Unicode character.

Define ownership, lifetime, and permitted mutation of every buffer or
reference crossing the bridge. In particular, an output operation must
capture the submitted text before returning, so subsequent Wasm buffer
reuse cannot change queued output. State when input storage can be reused
and ensure the program does not retain invalid references. Individual
output writes must preserve complete Unicode characters: correct
concatenation alone is insufficient if separate writes encode isolated
surrogate halves.

## Inputs, chunking, and executions

An input file is any finite byte sequence containing valid UTF-8, including
the empty file. Define validity using the encoding specification,
independently of the program's output or decoder implementation.

Permit every finite partition of the input into ordered, nonempty raw
buffers. Every byte occurs exactly once and in order; the empty file has
no raw buffers. A multibyte character may cross any raw buffer boundary.
Node's encoded reader decodes statefully across those boundaries.

Decoded text deliveries need not correspond one for one with raw buffers.
The bridge may further split text deliveries at complete-character
boundaries to respect implementation limits. No correctness argument may
depend on a particular Node read size, on line-aligned chunks, or on the
whole file fitting in Wasm memory. Empty text deliveries, if permitted by
the bridge model, have no transformation effect. All delivered text must
be in order, without loss or duplication.

The execution model must include both Wasm execution and host transitions
between calls. In particular, it must express persistent module state,
callback invocation and return, pending output, asynchronous completion,
and closing. Proving isolated callbacks return correctly is not sufficient
to establish the whole-file theorem.

## Assumptions and trusted boundary

We assume that Node, the JavaScript and Wasm runtimes, and the bridge
correctly implement their stated behavior in this scenario. The bridge's
JavaScript source and any builtin implementation need not be formally
verified in this project. Agreement between Talos semantics and runtime
WebAssembly remains a stated trust boundary. Pin the semantics and tools
used for the proof and report relevant gaps or discrepancies encountered.

We assume Node's UTF-8 decoding agrees with [LAWS.bend](../LAWS.bend).
The accepted [Lean translation](../candidates/spec-lean/Utf8Laws.lean) may
be reused, along with checked mathematical results from the repository.
A full audit of that specification is not a prerequisite; report any
discrepancy noticed incidentally.

The bridge and API contracts must describe individual operations and
their allowed effects independently of this program. They should cover:

- Stream creation, options, handles, and callback registration.
- Ordered, stateful UTF-8 decoding and finalization before input close.
- Faithful conversion between JavaScript strings and the chosen Wasm
  representation, including any splitting and storage effects.
- Imported calls' effects on Wasm and host state, including what they
  leave unchanged, their return values, and their possible outcomes.
- UTF-8 encoding of submitted text, FIFO write acceptance and completion,
  and output closing only after accepted writes finish.
- The scheduling and progress conditions under which pending work runs.

These contracts must not assume that the Wasm program prefixes lines
correctly, selects the right output handle, or obeys its interface.
Those are proof obligations about the program.

There are no input or output errors, memory exhaustion, or other resource
failures. The input is fixed, the output is a separate destination, and
filesystem aliasing and concurrent file changes are excluded. Successful
pending I/O and scheduled callbacks eventually make progress. State this
as progress of operations, rather than assuming program completion.

Backpressure is ignored. A write returning `false` still accepts and
queues its text; it does not drop data. Sufficient resources and progress
allow accepted writes to finish. No bounded-memory or throughput guarantee
is required for the host's output queue.

Resource assumptions do not excuse invalid memory access, overflowing
index arithmetic, invalid casts, or other program-induced traps. Prove
the relevant bounds and interface preconditions. If a delivery has a
size bound, specify it explicitly and explain how the bridge splits
larger text while preserving complete characters. Do not impose a
whole-file size bound merely to fit a pointer or counter.

GC may be modeled with abstract allocation without simulating collection.
Such a model does not establish bounds on retained memory, collection
latency, or behavior under exhaustion.

## Proof goals

Let `decodeUtf8` and `encodeUtf8` denote the specified whole-text decoding
and encoding. The central theorem must establish:

> For every valid UTF-8 input `B`, every allowed raw buffer partition and
> bridge text delivery, and every execution permitted by the stated
> bridge and progress contracts, the Wasm program eventually completes
> without trapping, and its completed output bytes are exactly
> `encodeUtf8(prefixLines(decodeUtf8(B)))`.

The output must itself be valid UTF-8. Equality is measured after all
accepted writes finish, not when input closes or an imported close
operation returns. The statement must rule out erroneous completed
outcomes as well as exhibit eventual success.

Also prove existence of permitted successful executions for every valid
input and allowed partition, with a realizable bridge delivery schedule.
Exhibit a concrete host model or equivalent construction satisfying the
contracts. This guards against vacuity from impossible preconditions or
inconsistent API assumptions. The implementation's initialization and
memory layout must actually satisfy the program theorem's hypotheses.

## Expected proof structure

Keep the following layers identifiable:

1. **Independent text specification.** Formalize `prefixLines`, UTF-8
   validity, and the representation relation. Prove the needed encoding
   and UTF-16 facts, or reuse checked proofs.
2. **Streaming algorithm.** Prove that processing chunks yields the
   whole-text transformation, regardless of allowed chunk boundaries.
   An implementation may remember whether the next character begins a
   line, but that state must not define the expected result.
3. **Wasm implementation.** Prove against Talos semantics that the module
   realizes the streaming algorithm, maintains its state across calls,
   respects memory and reference invariants, makes the specified host
   calls, and terminates each callback without trapping.
4. **Combined execution.** Derive eventual completion and the final byte
   result from the module proofs, bridge contracts, and progress.

Mathematical properties such as encoding composition, representation
correctness, and partition independence are obligations to prove, not
assumptions to place in the bridge contract. Proof automation and shared
infrastructure may be developed as needed; their initial development cost
is not a reason to weaken the theorem.

## Deliverables and scope

Provide a runnable Wasm module and JavaScript bridge, reviewable formal
specifications and API assumptions, checked Lean proofs of the target
results, and reproducible build and verification instructions.

Identify exactly which module the theorems concern and how it is connected
to the shipped `.wasm` bytes. State every trusted parser, printer,
compiler, or translation step; do not claim a verified artifact connection
where only testing or tool trust supplies it. The target results must not
be admitted or assumed. Include checks for proof holes and unexpected
axioms, and independent kernel checking following the lessons of the
existing candidate developments.

Use executable examples and bridge/runtime tests to exercise empty input,
trailing and consecutive LFs, CRLF, supplementary characters, raw splits
inside UTF-8 sequences, and text splits immediately after LF. Such tests
supplement the universal proofs and check the trusted boundary; they do
not replace either.

Error recovery, concurrent copier instances, reentrant callbacks, bounded
resource use, performance, timing behavior, and verification of Node or
its garbage collector are outside this demo. Security-layer verification,
tenant isolation, and noninterference are possible future applications,
not claims of this project.

The user reviews the specification. Write implementations and proofs for
maintenance by future coding-agent sessions. Use subagents for suitable
separable work, choosing cheaper models where sufficient. The user makes
commits; do not commit unless asked.
