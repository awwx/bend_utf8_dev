# UTF-8 copier proof demo

The intended contract and scope are in [FRAMING.md](FRAMING.md). The Lean
model concerns the two callback programs in [good.mjs](good.mjs) and
[bad.mjs](bad.mjs). It does not establish a source-to-model refinement or
verify Node itself.

## Checking

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
elan toolchain install leanprover/lean4:v4.35.0
./check.sh
```

The checker pins Lean 4.35.0, copies the dependency sources into a new
`mktemp` directory, compiles them there in dependency order, and removes
the temporary files on exit. Existing repository `.olean` files are never
used. It rejects proof holes, added axioms, native decision procedures,
and unsafe/external escape hatches in the compiled sources. It also
prints and checks the target theorems' axiom dependencies, permitting only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Foundation

This development reuses the repository's pure Lean UTF-8 decoder proofs.
The specification is copied directly from
[`candidates/spec-lean/Utf8Laws.lean`](../candidates/spec-lean/Utf8Laws.lean),
the accepted translation of `LAWS.bend`. The executable reference decoder
and its checked correctness proof come from
[`candidates/pure-lean`](../candidates/pure-lean).
This keeps the UTF-8 foundation and stream reasoning in one proof
assistant, without introducing a second cross-language translation or
assuming the desired copying property.

[`Utf8Roundtrip.lean`](Utf8Roundtrip.lean) defines valid files as finite
concatenations of sequences that satisfy the encoding specification.
The empty file is valid. Its `valid_roundtrip` theorem proves that decoding
and re-encoding any valid file recovers its bytes; this is a mathematical
lemma proved from the decoder laws, not an API premise.

## Shared program and API model

[`StreamModel.lean`](StreamModel.lean) uses a small callback language and
one stream machine for both programs. A program selects read/write
options and either writes its text argument or binds the result of a
complete-buffer `toString` and writes that value. Stream construction,
handle bindings, and data/close listener registration are elaborated
before delivery begins. This is an abstraction of those operations,
rather than a general JavaScript interpreter.

The contracts are modeled as definitions and transition rules, not
extra Lean axioms. Their agreement with Node is an environmental premise:

* An allowed input partition contains ordered nonempty buffers whose
  concatenation is the fixed input; the empty file has no buffers.
* An encoded reader carries decoder state between buffers and finalizes
  the decoder before normal input close. Empty decoder emissions remain
  as harmless empty delivery/write placeholders in the model. A raw reader delivers buffers,
  whose `toString` operation starts and finalizes a fresh decoder.
* Read encoding defaults to buffers; write encoding defaults to UTF-8.
  UTF-8 is the only supported write encoding.
* Each callback runs atomically, and callbacks enqueue writes in delivery
  order. A write accepts all encoded bytes with either Boolean return
  value. Pending writes finish in FIFO order, with flushing allowed
  between callbacks. Input close requests output close; output becomes
  done only after the queue drains.
* An execution may stutter for arbitrary finite durations. From every
  unfinished time, a later actual transition occurs. A decreasing rank
  proves eventual completion under that progress premise; completion is
  not itself a premise.

Text is a list of Unicode scalar values, abstracting decoder-produced
JavaScript UTF-16 strings. `textEvents_scalar` proves that each individual
encoded-reader delivery contains only whole scalars. Thus a supplementary
character represents its complete surrogate pair within one delivery;
the abstraction never splits that pair across writes. UTF-8 string
writing is `encodeText`, and `encodeText_append` proves composition
across deliveries. Arbitrary JavaScript strings containing isolated
surrogates are outside this abstraction.

`good_copy` quantifies over every valid file, allowed partition, and
execution satisfying these shared transition and progress rules. It
establishes eventual output completion and byte equality. Bytes are
compared after completion, not when the input close callback returns.

The model excludes errors, resource exhaustion, destination aliasing,
concurrent file changes, and text transformations. Ignoring backpressure
relies on unbounded successful queuing and progress; it is not a resource
or performance guarantee. Node implementation correctness and the
source-to-model correspondence remain assumed/out of scope as specified
in the framing document.

`executions_exist` supplies an eager successful scheduler for every
program and partition, establishing that the universal execution result
is nonvacuous. `bad_counterexample` establishes the valid input
`C2 A9`, permitted partition `[C2], [A9]`, both independent decodings to
`U+FFFD`, and an execution whose completed output is
`EF BF BD EF BF BD`, unequal to the input. It uses the same stream
machine and progress condition as `good_copy`.

The axiom audit covers `valid_roundtrip`, `textEvents_scalar`, `good_copy`,
`executions_exist`, and `bad_counterexample`. The successful final line is
`ALL COPIER CHECKS PASSED`.
