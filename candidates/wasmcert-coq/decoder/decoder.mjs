// Thin JS wrapper around decoder.wasm (printed from the Rocq term
// `decoder_module` by `make decoder.wasm`).  Unverified glue.  Its only logic:
//  - one module instance, shared by all calls (the module keeps no state
//    between calls: the decoder state is the i32 value passed in and out);
//  - decode_buffer splits the input into chunks of at most IN_MAX = 65536
//    bytes (justified by the spec's split-independence law), copies each
//    chunk to linear memory at IN = 0, calls `decode`, and reads the
//    UTF-16LE output at OUT = 65536 with TextDecoder('utf-16le');
//  - decode_done calls `done` and reads its output the same way.
import { readFileSync } from 'node:fs';

const IN = 0, IN_MAX = 65536, OUT = 65536;

export async function load() {
  const bytes = readFileSync(new URL('./decoder.wasm', import.meta.url));
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const ex = instance.exports;
  const td = new TextDecoder('utf-16le', { ignoreBOM: true });
  const text = (nbytes) => td.decode(new Uint8Array(ex.memory.buffer, OUT, nbytes));
  return {
    decode_start_state: () => ex.start(),
    decode_buffer(state, u8) {
      const parts = [];
      const mem = new Uint8Array(ex.memory.buffer);
      for (let p = 0; p < u8.length || p === 0; p += IN_MAX) {
        const chunk = u8.subarray(p, Math.min(p + IN_MAX, u8.length));
        mem.set(chunk, IN);
        const [st, nbytes] = ex.decode(state, chunk.length);
        state = st;
        parts.push(text(nbytes));
        if (u8.length === 0) break;
      }
      return [state, parts.join('')];
    },
    decode_done: (state) => text(ex.done(state)),
  };
}
