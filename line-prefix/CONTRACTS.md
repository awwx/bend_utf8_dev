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

The bridge forwards each immutable JavaScript string unchanged to `data(text)`.
It does not calculate a length, filter empty strings, split text, or inspect
surrogates. Each delivered string represents complete scalar encodings, as
supplied by Node's stateful UTF-8 reader. Its UTF-16 length must be representable
as an unsigned i32, matching the native string-length interface. This is not a
4096-unit delivery limit: the tested Node runtime's maximum string length is
536,870,888 units, already below the proof's `2^32` bound. There is no bound on
the total file length or number of events.

Wasm obtains the length from the native builtin. It selects successive slices
of at most 4096 units, shortening a slice by one when its tentative end falls
between a surrogate pair. `Chunking.lean` proves that this concrete boundary
test preserves complete scalar encodings and consumes all input in order.
Empty deliveries produce no writes. The bridge has no chunk-size setting.

For each internal slice, Wasm allocates a mutable i16 input array and an output
array with three times that capacity. Both are local references. Prefixing can
add at most two units per input unit. Wasm computes and proves all substring
and array bounds, including the absence of i32 arithmetic overflow. The helper
is exported as `_chunk` for proof entry; the Node bridge calls only `data`.
There is no linear-memory buffer or JavaScript text conversion loop.

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

The module also imports five native builtins from `wasm:js-string`. The array
type is a mutable i16 GC array declared in its own recursion group.

| Builtin | Effect |
|---|---|
| `length(string) -> i32` | Return the UTF-16 unit count; preserve the entire store. |
| `charCodeAt(string, index) -> i32` | Return the unsigned UTF-16 unit at the index; trap outside the string and preserve state. |
| `substring(string, start, stop) -> string` | Capture a new immutable substring. Clamp stop at the string length; return empty for reversed ranges or a start beyond the string. This operation itself does not protect surrogate pairs. |
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

The runtime is instantiated with `{ builtins: ['js-string'] }`; these five
imports are supplied by the engine, not JavaScript polyfills. Their agreement
with the formal operation models is trusted, as is Node's UTF-8 decoding and
encoding. The builtin definitions are documented in the
[WebAssembly JS String Builtins specification](https://github.com/WebAssembly/js-string-builtins/blob/main/proposals/js-string-builtins/Overview.md).

## Delivery and progress

`init` creates both streams and registers both listeners before any data
callback runs. The encoded reader decodes UTF-8 statefully across arbitrary
nonempty raw byte buffers, including boundaries inside multibyte sequences.
It finalizes decoding before normal input close. String delivery preserves
scalar order and multiplicity. The bridge forwards those events unchanged;
all additional splitting occurs within Wasm. The formal delivery abstraction
permits any faithful sequence of representable Node strings. Existence is
proved for every such sequence, not by assuming the forwarder manufactures
a particular grouping.

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
