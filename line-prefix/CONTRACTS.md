# Bridge and execution contracts

These are assumptions about Node, its Wasm runtime, `bridge.mjs`, and the
`wasm:js-string` builtins. The transformation, representation properties,
chunk composition, Unicode encoding properties, and Wasm execution are proof
obligations, not bridge assumptions.

## Representation and ownership

The specification describes lists of Unicode scalar values: integers from
0 through 0x10FFFF excluding 0xD800 through 0xDFFF. JavaScript strings and
Wasm arrays represent these as UTF-16 code units. `Utf16.lean` defines the
encoding, including supplementary characters' high/low surrogate pairs,
and proves that processing the code units implements the scalar specification.

The bridge passes an immutable JavaScript string and its UTF-16 length to
`data`. A delivery contains at most 4096 UTF-16 units and comprises complete
scalar encodings. The bridge splits longer strings with `slice`, inspecting
only split boundaries to avoid separating a surrogate pair. Its configurable
chunk target is between 1 and 4096 units. A target of 1 still delivers a
surrogate pair together as two units; the absolute 4096-unit limit always
holds. This also provides a concrete singleton-scalar delivery schedule. Empty strings
may be omitted; the Wasm callback also supports empty strings.

Wasm allocates a mutable i16 input array of that length and a mutable i16
output array with three times that capacity. Both are local references:
the module does not retain them after callback return. Prefixing can add at
most two units per input unit. There is no linear-memory buffer or per-unit
JavaScript conversion loop.

The input string remains immutable. `intoCharCodeArray` copies its units
into the input array. `fromCharCodeArray` captures the specified output
range as a new immutable string before returning. Neither output queuing
nor later callbacks retain a mutable alias to the submitted text.

Talos models GC allocation with an append-only heap, and the host model
represents immutable strings by indices into an append-only string table.
These are mathematical representations, not retained JavaScript data
structures in the bridge. Real runtimes may collect unreachable objects.
No heap size or collection latency bound is claimed.

## Imported operations

The `bridge` imports adapt Node's API. Apart from the specified host effects,
they preserve Wasm memory, globals, tables, and GC objects. Calls do not
reenter Wasm.

| Import | Effect |
|---|---|
| `create_input() -> handle` | Create the UTF-8 encoded reader for the fixed input; return handle 0. |
| `create_output() -> handle` | Create the separate UTF-8 output; return handle 1. |
| `on_data(input, callback)` | Register the identified data export on the input; callback token 1 denotes `data`. |
| `on_close(input, callback)` | Register the identified close export; callback token 2 denotes `close`. |
| `write(output, string)` | Append the immutable string's UTF-8 encoding to the output's FIFO queue. |
| `end(output)` | Request output completion after all queued writes finish. |

The module also imports two native builtins from `wasm:js-string`. The array
type is a mutable i16 GC array declared in its own recursion group.

| Builtin | Effect |
|---|---|
| `intoCharCodeArray(string, array, start) -> count` | Copy all UTF-16 units into the existing array at `start`; return the string length. Preserve all other array elements and state. Trap on invalid references or insufficient space. |
| `fromCharCodeArray(array, start, stop) -> string` | Capture units in the half-open range `[start, stop)` as a new immutable string. Preserve the array and other Wasm state. Trap on invalid references or an invalid range. |

Indices are unsigned i32 values; bounds checks use mathematical addition,
without wrapping. The explicit models in `Wasm.lean` state these operations'
behavior independently of prefixing. Correct references, array types, unit
bounds, indices, and lengths are program proof obligations. The string table
and GC slots used for text represent 16-bit code units, not arbitrary scalars.
Agreement with the native builtins is asserted on these representable states;
the callback proofs establish the required bounds for every fresh string and
array they access and preserve the rest of the heap.

The builtins accept arbitrary JavaScript UTF-16 strings, including unpaired
surrogates. Our theorem instead establishes that every submitted output is
an encoding of complete scalars. Consequently, separate Node writes cannot
encode isolated halves of a pair. The formal host records captured UTF-16
payloads; the combined model relates them to scalar text and specified UTF-8.

The concrete bridge rejects invalid handles, callback tokens, and non-string
writes. The proof establishes correct handles and registrations; neither host
contract assumes the writes contain prefixes. Node's `write` return value is
ignored: false still accepts the complete write. The Wasm import returns void.

The runtime is instantiated with `{ builtins: ['js-string'] }`; these two
imports are supplied by the engine, not JavaScript polyfills. Their agreement
with the formal operation models is trusted, as is Node's UTF-8 decoding and
encoding. The builtin definitions are documented in the
[WebAssembly JS String Builtins specification](https://github.com/WebAssembly/js-string-builtins/blob/main/proposals/js-string-builtins/Overview.md).

## Delivery and progress

`init` creates both streams and registers both listeners before any data
callback runs. The encoded reader decodes UTF-8 statefully across arbitrary
nonempty raw byte buffers, including boundaries inside multibyte sequences.
It finalizes decoding before normal input close. String delivery preserves
scalar order and multiplicity, regardless of subsequent complete-character
splitting by the bridge.

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
permit out-of-bounds array operations, wrapping index arithmetic, invalid
references, or program-induced traps.
