# Bend UTF-8 streaming decoder

The decoder provides a starting state and two functions:

```
def decode_start_state() -> DecodeState()
```

`decode_start_state` returns the decoder state to pass with the first
buffer.

`DecodeState()` is opaque: callers only pass it from one call
to the next.  This follows Bend's convention for state that may be
affine, like a `File` handle or an `App.run` state: each call takes
the state and hands back the next one beside its result, so the state
is never needed twice.  Today's `DecodeState()` happens to be copyable,
but callers shouldn't rely on that.

```
def decode_buffer(state: DecodeState(), +buffer: List<&2, U32>,
  -valid: {decode_buffer.all_bytes(buffer) == True{} : Bool}) ->
  DecodeState() & String
```

Given the current decoder state, the next buffer to decode, and a
proof that the buffer contains only byte values, `decode_buffer`
returns the updated decoder state and a string containing the
characters completed by this buffer.

Bytes of a sequence that isn't finished yet, such as a multibyte
character split across buffers, are carried in the decoder state for
the next buffer.

Invalid UTF-8 byte sequences result in a Unicode replacement character
(U+FFFD) being generated, following the Unicode "maximal subpart"
recommendation.

```
def decode_done(state: DecodeState()) -> String
```

At the end of input, `decode_done` is called with the decoder state
and returns the final text of the decoding result.  This will be an
empty string if the last buffer ended in a complete character, and a
replacement character if the last buffer ended in an incomplete
character.

## Files

* `utf8.bend`: the implementation.
* `LAWS.bend`: the specification.
* `PROOF.bend`: the proofs that the implementation meets the
  specification.

To verify, run `bend PROOF.bend`; it prints "ALL PROOFS CHECK".

## Specification

In the specification written in `LAWS.bend`, we start with a spec of
the UTF-8 decoding of the complete input, where any incomplete
character at the end of the input results in a Unicode replacement
character.  The law `decodes_examples` gives worked examples.

We then have three requirements for the streaming implementation:

1. `utf8_decodes`: the concatenation of the text returned by streaming
is always the same as decoding the complete input (the concatenation
of the buffers fed to the streaming implementation).  That is, it
doesn't matter how the complete input is split up, we always end up
with the same final result.

2. `utf8_decode_buffer_safe`: text returned by `decode_buffer` never
has to be taken back.  Whatever bytes follow, the complete input
decodes to text that begins with the text returned so far.

3. `utf8_decode_buffer_prompt`: all fully completed characters so far
(including generated replacement characters) are immediately returned
by each call to `decode_buffer`.  This prevents, for example, an
implementation from carrying all the input buffers in the decoder
state and then returning the entire decoded text from `decode_done`.

## Demo

`io_http_streaming_fetch.bend` contains a version of
https://github.com/bendlang/bend/tree/v2.0.40/demos/io_http_fetch
modified to use the streaming decoder: on a slow connection, text from
the response body is printed as it becomes available instead of
waiting for the entire response body to be returned before printing
anything.  The demo isn't covered by the proofs.
