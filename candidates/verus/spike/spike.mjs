// Thin JS wrapper around spike.wasm (built from spike.rs).
import { readFileSync } from 'node:fs';

const bytes = readFileSync(new URL('./spike.wasm', import.meta.url));
const { instance } = await WebAssembly.instantiate(bytes, {});
const x = instance.exports;

export function is_surrogate_code_point(cp) {
  return x.is_surrogate_code_point(cp >>> 0) !== 0;
}

export function count_non_ascii(u8) {
  const base = x.__heap_base.value;       // first free byte above the Wasm data/stack
  const need = base + u8.length;
  const have = x.memory.buffer.byteLength;
  if (need > have) x.memory.grow(Math.ceil((need - have) / 65536));
  new Uint8Array(x.memory.buffer, base, u8.length).set(u8);
  return x.count_non_ascii(base, u8.length) >>> 0;
}
