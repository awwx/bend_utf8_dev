// Thin wrapper around spike.wasm. No allocator in the module: to pass bytes we grow the memory
// by whole pages and write the input at the start of the new pages.
import { readFileSync } from 'node:fs';

const wasmPath = new URL('./target/wasm32-unknown-unknown/release/spike.wasm', import.meta.url);
const { instance } = await WebAssembly.instantiate(readFileSync(wasmPath), {});
const x = instance.exports;
const PAGE = 65536;

export function is_surrogate_code_point(cp) {
  return x.spike_is_surrogate_code_point(cp >>> 0) !== 0;
}

export function count_non_ascii(bytes) {
  const pages = Math.max(1, Math.ceil(bytes.length / PAGE));
  const base = x.memory.grow(pages) * PAGE; // returns old size in pages
  new Uint8Array(x.memory.buffer, base, bytes.length).set(bytes);
  return x.spike_count_non_ascii(base, bytes.length) >>> 0;
}
