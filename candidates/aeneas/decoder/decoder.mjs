// Thin, unverified wrapper around decoder.wasm (verified core: decode_buffer / decode_done
// of src/lib.rs).  Logic here: (1) reserve, once, a fixed memory region (grown past the
// module's own memory): input chunk, output code points, one u32 state slot; (2) feed the
// input in chunks of at most CHUNK bytes (justified by split independence of the spec);
// (3) turn the code points the core wrote into a JS string.  The state is a JS number.
import { readFileSync } from 'node:fs';

const CHUNK = 1 << 16;               // input bytes per call into the module
const OUT_CAP = 2 * CHUNK;           // core needs out.len >= 2 * in.len
const PAGE = 65536;

export async function load() {
  const bytes = readFileSync(new URL('./decoder.wasm', import.meta.url));
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const x = instance.exports;
  const need = CHUNK + 4 * OUT_CAP + 4;
  const base = x.memory.grow(Math.ceil(need / PAGE)) * PAGE;
  const IN = base, OUT = base + CHUNK, ST = OUT + 4 * OUT_CAP;
  const mem = () => x.memory.buffer;   // memory never grows again, but be safe

  function cpsToString(n) {
    const cps = new Uint32Array(mem(), OUT, n);
    let s = '';
    for (let j = 0; j < n; j += 8192) {
      s += String.fromCodePoint.apply(null, cps.subarray(j, Math.min(n, j + 8192)));
    }
    return s;
  }

  function decode_start_state() { return x.utf8_start() >>> 0; }

  function decode_buffer(state, buf) {
    let st = state >>> 0;
    const parts = [];
    for (let off = 0; off < buf.length || (off === 0 && parts.length === 0); off += CHUNK) {
      const len = Math.min(CHUNK, buf.length - off);
      new Uint8Array(mem(), IN, len).set(buf.subarray(off, off + len));
      const k = x.utf8_decode_buffer(st, IN, len, OUT, OUT_CAP, ST) >>> 0;
      st = new Uint32Array(mem(), ST, 1)[0];
      parts.push(cpsToString(k));
      if (buf.length === 0) break;
    }
    return [st, parts.join('')];
  }

  function decode_done(state) {
    const k = x.utf8_decode_done(state >>> 0, OUT, OUT_CAP) >>> 0;
    return cpsToString(k);
  }

  return { decode_start_state, decode_buffer, decode_done };
}
