# Proving correct use of Node streams for UTF-8 text copying

This project is a formal verification demo about using Node's stream APIs
correctly for UTF-8 decoding. A program reads a valid UTF-8 text file, obtains
text that could be manipulated, and writes another UTF-8 file. The demo
performs no text manipulation, so its required result is byte-for-byte
equality of the input and completed output.

The goal is to prove that a model of [good.mjs](good.mjs) meets this
requirement and to prove a counterexample for a model of
[bad.mjs](bad.mjs), using the same semantics and API specifications.
This document frames the work; it does not claim that these proofs exist
yet.

## Programs and the decoding mistake

The good program creates a read stream with `encoding: 'utf8'`. Its
`data` callback receives text and writes that text to a UTF-8 write
stream. Its input `close` callback closes the output stream.

The bad program creates a read stream without an encoding. Its `data`
callback receives a buffer, calls `buffer.toString('utf8')`, and writes
the resulting text. Its output uses the default UTF-8 encoding, and it
has the same input `close` callback.

The bad program represents a plausible mistake: the programmer wants
text, notices that the read stream supplies buffers, and decodes each
buffer independently. A multibyte character can straddle buffers. Each
independent conversion treats its buffer as complete input, so it cannot
recover the character using bytes from the next buffer.

Passing buffers directly to the output would change this scenario:
the demo deliberately obtains decoded text at the point where a real
application could manipulate it.

## Proof goals

An input file is a finite sequence of bytes containing valid UTF-8.
Validity must be defined using the encoding specification, independently
of the desired copying result. The empty file is valid input.

The API model permits any finite partition of the input into ordered,
nonempty buffers. Every input byte occurs exactly once and in order.
The empty file has no input buffers. This is an intentional API
abstraction; no particular Node version's preferred read size restricts
the allowed partitions. Decoded text events need not correspond one for
one with raw buffers: an incomplete character may require more bytes
before any text can be emitted.

The good-program theorem must establish that, for every valid input,
every allowed partition and every permitted execution, the program
eventually completes and the final output bytes equal the input bytes.
Eventual completion relies on the successful-I/O progress assumptions
below. Equality is measured after output writes finish, rather than at
the instant the input closes or the output close method returns.

The bad-program theorem must exhibit a valid input and a permitted
execution that completes with different output bytes. The intended
witness is:

```text
Input bytes:          C2 A9                    (U+00A9, ©)
Input buffers:        [C2], [A9]
Decoded strings:      U+FFFD, U+FFFD
Final output bytes:   EF BF BD EF BF BD
```

The proof must establish input validity, permission for this buffer
partition, the two decoding results, and the unequal completed output.
It need not claim that the bad program fails on every partition.

## Assumed foundation

We assume Node's JavaScript runtime and modules are bug free. We will
find or write specifications for the language features and APIs used by
the modeled programs, and assume those specifications correctly describe
their behavior within this scenario.

We assume Node's UTF-8 decoding agrees with the specification in
[LAWS.bend](../LAWS.bend). The existing translations in
[Utf8Laws.lean](../candidates/spec-lean/Utf8Laws.lean) and
[Utf8Laws.v](../candidates/spec-rocq/Utf8Laws.v) may be treated as correct
translations. Auditing those specifications is not this demo's focus.
Report any discrepancy noticed incidentally, without making a full
specification audit a prerequisite.

There are no input or output errors, memory exhaustion, or other resource
constraints. Successful pending I/O and scheduled callbacks eventually
make progress. The input is a fixed byte sequence and the output is a
separate destination; filesystem aliasing and concurrent file changes
are outside the model.

The demo ignores backpressure. The API specification must describe the
fact that a write can be accepted and queued even when `write` returns
false. Under the resource and progress assumptions, queued writes can
finish. Ignoring that return value must not be modeled as dropping data.

## Shared semantics and API contracts

The proof language and existing semantics to reuse remain open choices.
A small operational model of the necessary JavaScript subset and Node
APIs is acceptable. Both programs must run under the same rules, with
their different stream options and callback bodies determining their
different behavior.

The model should cover the following behavior, at whatever level of
abstraction is sufficient for the proofs:

- Stream construction and default encoding options.
- Bindings, callback registration, callback arguments, local computation,
  and method calls used in these programs.
- Ordered delivery of bytes, stateful decoding for an encoded read
  stream, and independent complete-buffer decoding for `toString`.
- Event ordering that ensures listeners are registered before delivery,
  all text including decoder finalization is delivered before normal
  input `close`, and callbacks perform their writes in order.
- UTF-8 encoding of string writes, ordered queuing and completion of
  output bytes, and output closing after queued writes finish.
- Sufficient progress to reach a completed output under the stated
  successful-I/O assumptions.

These contracts should describe individual operations independently of
either program. In particular, an assumption that the good program
copies correctly would assume the theorem we intend to prove.

JavaScript strings use UTF-16 code units, whereas the UTF-8 specifications
represent text as code points. The model must account for this
difference. It may model UTF-16 explicitly or use a justified abstraction
for strings produced by the decoder. In particular, the stream contract
must preserve complete Unicode characters in each text delivery: merely
requiring the concatenation of delivered strings to be correct is not
enough if individual writes could receive separate surrogate halves.

## Proof structure

The expected argument for the good program is that the read stream
delivers the specified decoding of all input bytes, the callbacks write
exactly that text in order, and closing the output allows those writes
to finish. Encoding the resulting text then recovers the original valid
UTF-8 bytes.

The UTF-8 round-trip property and any required encoding composition
lemmas are mathematical obligations to prove or obtain from checked
proofs. They should not be introduced as assumptions about the copying
program. API behavior, mathematical lemmas, and program conclusions
should remain identifiable in the formal development.

The bad-program proof follows the same callback and write rules, but
uses complete-buffer decoding separately on each delivered buffer. It
derives the concrete replacement characters and resulting output bytes
for the witness above.

## Scope and deliverables

Correspondence between the modeled programs and the actual `.mjs` source
files is explicitly out of scope. There is no requirement to build a
JavaScript parser, verify a translation, or prove source-level
refinement. The result will be a proof about the program models under
the stated semantics and assumptions.

Error recovery, resource bounds, backpressure handling, performance,
general text transformations, and correctness of Node's implementation
are also outside the proof obligations. Malformed whole input files
are outside the good-program theorem, but malformed or incomplete
individual buffers remain essential to the bad-program counterexample.

The completed demo should provide reviewable API assumptions, the shared
model and both modeled programs, checked proofs of the good-program
theorem and bad-program counterexample, and reproducible instructions
for checking them. Any remaining unproved premises must be stated
explicitly; the two target results must not be admitted or assumed.

Use subagents for suitable separable work, choosing cheaper models and
lower effort where sufficient. Keep the specification and proof interfaces
consistent across delegated work. The user makes commits; do not commit
unless asked.
