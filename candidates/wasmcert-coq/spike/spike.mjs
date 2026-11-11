// Thin JS wrapper around spike.wasm (generated from the Rocq term by
// `make spike.wasm`).  Unverified glue: it copies the input into Wasm
// memory at offset 0 and converts results.
import { readFileSync } from 'node:fs';

const bytes = readFileSync(new URL('./spike.wasm', import.meta.url));
const { instance } = await WebAssembly.instantiate(bytes, {});
const ex = instance.exports;

export function is_surrogate_code_point(cp) {
  return ex.is_surrogate_code_point(cp | 0) !== 0;
}

export function count_non_ascii(u8) {
  const mem = ex.memory;
  const need = u8.length;
  if (need > mem.buffer.byteLength) {
    // The module does not grow memory itself; grow from the host side.
    mem.grow(Math.ceil((need - mem.buffer.byteLength) / 65536));
  }
  new Uint8Array(mem.buffer, 0, need).set(u8);
  return ex.count_non_ascii(0, need) >>> 0;
}
