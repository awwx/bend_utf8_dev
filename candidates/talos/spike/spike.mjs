// Thin JS wrapper around spike.wasm (the bytes the Lean theorems are tied to;
// see REPORT.md for the trusted chain).
import { readFileSync } from 'node:fs';

const bytes = readFileSync(new URL('./spike.wasm', import.meta.url));
const { instance } = await WebAssembly.instantiate(bytes, {});
const ex = instance.exports;

export function is_surrogate_code_point(cp) {
  return ex.is_surrogate_code_point(cp | 0) !== 0;
}

// Copies the bytes to address 0 of linear memory, growing it if needed.
// The theorem covers ptr + len <= memory size, which this guarantees.
export function count_non_ascii(u8) {
  const need = Math.ceil(u8.length / 65536) - ex.memory.buffer.byteLength / 65536;
  if (need > 0) ex.memory.grow(need);
  new Uint8Array(ex.memory.buffer, 0, u8.length).set(u8);
  return ex.count_non_ascii(0, u8.length) >>> 0;
}
