import assert from 'node:assert/strict';
import { is_surrogate_code_point, count_non_ascii } from './spike.mjs';

// LAWS.bend is_surrogate_code_point_examples
const examples = [[0x0000, false], [0xD7FF, false], [0xD800, true],
                  [0xDC00, true], [0xDFFF, true], [0xE000, false]];
for (const [cp, want] of examples) assert.equal(is_surrogate_code_point(cp), want, cp.toString(16));
// extra: large / "negative" i32 values are read as unsigned
assert.equal(is_surrogate_code_point(0xFFFFFFFF), false);
assert.equal(is_surrogate_code_point(0x1D800), false);

const ref = (u8) => u8.reduce((n, b) => n + (b >= 0x80 ? 1 : 0), 0);
const enc = new TextEncoder();
const bufs = [
  new Uint8Array([]),
  new Uint8Array([0x41]),
  new Uint8Array([0x80, 0x7F, 0xFF, 0x00]),
  enc.encode('héllo wörld €𝄞'),
  Uint8Array.from({ length: 1000 }, (_, i) => (i * 37) & 0xFF),
  Uint8Array.from({ length: 200000 }, (_, i) => (i * 101) & 0xFF), // forces memory.grow
];
for (const b of bufs) assert.equal(count_non_ascii(b), ref(b), `len ${b.length}`);
// repeated calls on the same instance
assert.equal(count_non_ascii(new Uint8Array([0xC3, 0xA9])), 2);
assert.equal(count_non_ascii(new Uint8Array([0x61])), 0);
console.log('spike tests passed');
