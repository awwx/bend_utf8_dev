# UTF-8 copier proof demo

The intended contract and scope are in [FRAMING.md](FRAMING.md). The Lean
model concerns the two callback programs in [good.mjs](good.mjs) and
[bad.mjs](bad.mjs). It does not establish a source-to-model refinement or
verify Node itself.

## Checking

With [elan](https://github.com/leanprover/elan) and `bubblewrap` installed,
run from this directory as a non-root user:

```sh
elan toolchain install leanprover/lean4:v4.35.0
./check.sh
```

The checker refreshes its local copies of `Utf8Laws.lean` and
`Utf8Check.lean` from `lean/spec` and runs Lean's sandboxed comparator.
The comparator checks the statements against `CopierChallenge.lean`,
checks the proofs in Lean's kernel, and permits only `propext`,
`Classical.choice`, and `Quot.sound`. Pass `--paranoid` to also run the
bundled external checkers.

## Foundation

Both results apply to any decoder satisfying `node_characterization`
in [`Utf8Laws.lean`](../lean/spec/Utf8Laws.lean). The only clause needed
is `utf8_decodes`, which specifies the complete text after finalization.
The copier imports the UTF-8 specification and its mathematical proofs
from [`lean/spec`](../lean/spec).

[`Utf8Roundtrip.lean`](Utf8Roundtrip.lean) defines valid files as finite
concatenations of sequences that satisfy the encoding specification,
including the empty file. In [`CopierCheck.lean`](CopierCheck.lean),
`valid_roundtrip` proves that encoding any text related to a valid file
by `decodes` recovers the file's bytes.

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
  whose `toString` operation has the result specified for a fresh decoder
  fed that buffer and finalized. The model uses the equivalence of the results.
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

The comparator checks `valid_roundtrip`, `textEvents_scalar`, `good_copy`,
`executions_exist`, and `bad_counterexample`.
