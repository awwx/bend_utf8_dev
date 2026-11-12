// Thin JS wrapper around decoder.wasm (the bytes the Lean theorems are about;
// see Boundary.lean and REPORT.txt).
//
// Wrapper logic (all unverified):
//  - the decoder state is the i32 returned by the module, kept as a JS number;
//  - decode_buffer splits the input into chunks of at most CHUNK bytes
//    (justified by the spec's split-independence law), copies each chunk to
//    address IN = 0, calls the export with out = OUT, and reads the code
//    points the module wrote as little-endian u32 in [OUT, end);
//  - code points are turned into a JS string with String.fromCodePoint
//    (every output code point is a Unicode scalar: pure-lean decoded_scalar).
import { readFileSync } from 'node:fs';

// Memory layout.  check.sh reads the three "LAYOUT" lines and fails unless they
// equal the constants of the same names in Boundary.lean (the numbers the
// non-vacuity theorem is about); keep them plain decimal literals.
const CHUNK = 1048576;          // LAYOUT wrapperMaxChunk   (2^20; input area [IN, IN + CHUNK))
const IN = 0;                   // LAYOUT wrapperInputAddr
const OUT = 1048576;            // LAYOUT wrapperOutputAddr (output area [OUT, OUT + 8*CHUNK))

function cpsToString(u32, start, end) {
  let s = '';
  for (let i = start; i < end; i += 8192) {
    s += String.fromCodePoint.apply(null, u32.subarray(i, Math.min(end, i + 8192)));
  }
  return s;
}

export async function load() {
  const bytes = readFileSync(new URL('./decoder.wasm', import.meta.url));
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const ex = instance.exports;
  const mem = () => ex.memory.buffer;

  function decode_start_state() {
    return ex.decode_start_state();
  }

  function decode_buffer(state, buf) {
    let s = state;
    let text = '';
    for (let off = 0; off < buf.length || off === 0; off += CHUNK) {
      const chunk = buf.subarray(off, Math.min(buf.length, off + CHUNK));
      new Uint8Array(mem(), IN, chunk.length).set(chunk);
      const [s2, end] = ex.decode_buffer(s, IN, chunk.length, OUT);
      s = s2;
      text += cpsToString(new Uint32Array(mem()), OUT >>> 2, (end >>> 0) >>> 2);
      if (buf.length === 0) break;
    }
    return [s, text];
  }

  function decode_done(state) {
    const end = ex.decode_done(state, OUT) >>> 0;
    return cpsToString(new Uint32Array(mem()), OUT >>> 2, end >>> 2);
  }

  return { decode_start_state, decode_buffer, decode_done };
}
