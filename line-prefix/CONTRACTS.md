# Bridge and execution contracts

These are assumptions about Node, its Wasm runtime, and `bridge.mjs`.
The transformation, chunk composition, Unicode encoding properties, and Wasm
execution are proof obligations, not bridge assumptions.

## Representation and ownership

A text value is a list of Unicode scalar values: integers from 0 through
0x10FFFF excluding 0xD800 through 0xDFFF. A memory word represents one scalar
as an unsigned 32-bit little-endian integer. This is not UTF-16: the bridge
converts JavaScript strings by iterating complete code points.

The module has one 64 KiB memory page with no growth. A data delivery has
0 through 4096 scalars, stored consecutively beginning at byte 0. The bridge
may overwrite that input region between calls. It leaves other memory and
all module globals unchanged. The module owns the output region beginning
at byte 16384, with capacity for 12288 scalars. Both regions are reusable;
no reference to either region is retained by asynchronous output.

`write` captures the submitted words as immutable text before returning.
Each write encodes a sequence of complete scalars, so separate writes cannot
split a surrogate pair. The proof uses the accepted UTF-8 specification;
agreement of `String.fromCodePoint` and Node's string encoding with this
representation is trusted.

## Imported operations

Imports are under the `bridge` namespace. Arguments and handles have Wasm
i32 type. Apart from the specified effects, imports preserve Wasm memory,
globals, tables, and other instance state. Calls do not reenter Wasm.

| Import | Effect |
|---|---|
| `create_input() -> handle` | Create the UTF-8 encoded reader for the fixed input; return handle 0. |
| `create_output() -> handle` | Create the separate UTF-8 output; return handle 1. |
| `on_data(input, callback)` | Register the identified data export on the input; callback token 1 denotes `data`. |
| `on_close(input, callback)` | Register the identified close export; callback token 2 denotes `close`. |
| `write(output, pointer, length)` | Capture `length` scalar words at `pointer` and append their UTF-8 encoding to the output's FIFO queue. |
| `end(output)` | Request output completion after all queued writes finish. |

The concrete bridge rejects invalid handles, callback tokens, memory ranges,
and non-scalar output. Correct use of these interfaces by the module is a
proof obligation. The formal host logs individual calls and their captured
arguments; the scheduler interprets the successful stream operations.
Neither contract assumes that the writes contain the requested prefixes.

The return value of Node's `write` is ignored: a false value still accepts
the complete write. The imported Wasm operation has no return value.

## Delivery and progress

`init` creates both streams and registers both listeners before any data
callback runs. The encoded reader decodes UTF-8 statefully across arbitrary
nonempty raw byte buffers, including boundaries inside multibyte sequences.
It finalizes decoding before normal input close. The bridge splits decoded
strings into at most 4096 complete scalars and calls `data(length)` once per
chunk. Empty strings may be omitted; the Wasm callback also supports empty
chunks. Delivery preserves scalar order and multiplicity.

All callbacks run serially. Between callbacks, pending output may finish in
FIFO order. Host progress allows arbitrary finite delays but eventually
performs another pending operation whenever unfinished. Normal input close
invokes `close`; that requests output closing. Completion is the output's
`finish` event, after queued writes drain, not input close or return from
`end`.

Files are finite, input is valid UTF-8 and fixed, and output does not alias
input. There are no I/O failures or resource exhaustion. The implementation
reports errors but their recovery is outside the theorem. Ignoring
backpressure permits unbounded host queue growth. These assumptions do not
permit out-of-bounds memory operations, wrapping pointer arithmetic, or
program-induced traps.
