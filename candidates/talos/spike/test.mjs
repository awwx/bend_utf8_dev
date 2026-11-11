import assert from 'node:assert/strict';
import { is_surrogate_code_point as s, count_non_ascii as c } from './spike.mjs';

const ex = [[0x0000, false], [0xD7FF, false], [0xD800, true], [0xDC00, true], [0xDFFF, true], [0xE000, false]];
for (const [cp, want] of ex) assert.equal(s(cp), want, `cp ${cp.toString(16)}`);
assert.equal(s(0xFFFFFFFF), false);
const ref = (u8) => u8.reduce((n, b) => n + (b >= 0x80 ? 1 : 0), 0);
const bufs = [new Uint8Array([]), new TextEncoder().encode('hello'), new TextEncoder().encode('héllo wörld €😀'),
  Uint8Array.from({ length: 256 }, (_, i) => i), Uint8Array.from({ length: 200000 }, (_, i) => (i * 7919) & 0xff)];
for (const b of bufs) assert.equal(c(b), ref(b));
console.log('all tests passed');
