Bend UTF-8 streaming decoder

There are two functions provided:

```
def decode_buffer(state: DecodeState(), +buffer: List<&2, U32>,
  -valid: {decode_buffer.all_bytes(buffer) == True{} : Bool}) ->
  DecodeState() & String
```

Given the current decoder state, the next buffer to decode, and a
proof that the buffer contains only byte values, `decode_buffer`
returns the updated decoder state and a string containing the complete
characters available so far.

If any multibyte characters are split across buffers, the incomplete
character will be carried in the decoder state for the next buffer.

Invalid UTF-8 byte sequences result in a Unicode replacement character
being generated, following the Unicode "maximal subpart"
recommendation.

```
def decode_done(state: DecodeState()) -> String
```

At the end of input, `decode_done` is called with the decoder state
and returns the final text of the decoding result.  This will be an
empty string if the last buffer ended in a complete character, and a
replacement character if the buffer ended in an incomplete character.

In the specification written in LAWS.bend, we start with a spec of the
UTF-8 decoding of a complete buffer, where any incomplete character at
the end of the buffer results in a Unicode replacement character.

We then have two requirements for the streaming implementation:

1. The concatenation of the text returned by streaming is always the
same as decoding the complete buffer (the concatenation of the buffers
fed to the streaming implementation).  That is, it doesn't matter how
the complete input is split up, we always end up with the same final
result.

2. All fully completed characters so far are immediately returned by
each call to `decode_buffer`.  This prevents, for example, an
implementation from carrying all the input buffers in the decoder
state and then returning the entire decoded text from `decode_done`.

`io_http_streaming_fetch.bend` contains a vibecoded version of
https://github.com/bendlang/bend/tree/v2.0.40/demos/io_http_fetch
modified to use the streaming decoder: on a slow connection, text from
the response body is printed as it becomes available instead of
waiting for the entire response body to be returned before printing
anything.
