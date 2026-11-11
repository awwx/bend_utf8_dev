import assert from 'node:assert/strict';
import { is_surrogate_code_point as sur, count_non_ascii as cnt } from './spike.mjs';

// LAWS.bend examples
for (const [cp, want] of [[0, false], [0xD7FF, false], [0xD800, true], [0xDC00, true], [0xDFFF, true], [0xE000, false]])
  assert.equal(sur(cp), want, cp.toString(16));
// exhaustive over the whole u32 range edge neighbourhood and a sample sweep
for (let cp = 0; cp < 0x110000; cp++) assert.equal(sur(cp), cp >= 0xD800 && cp <= 0xDFFF);
assert.equal(sur(0xFFFFFFFF), false);

assert.equal(cnt(new Uint8Array([])), 0);
assert.equal(cnt(new Uint8Array([0x41, 0x7f])), 0);
assert.equal(cnt(new Uint8Array([0x80, 0x41, 0xff, 0xc3])), 3);
assert.equal(cnt(new TextEncoder().encode('héllo €🙂')), 2 + 3 + 4);
const big = new Uint8Array(200000).map((_, i) => (i * 7) & 0xff);
assert.equal(cnt(big), big.filter((b) => b >= 0x80).length);
assert.equal(cnt(big.subarray(5, 100)), big.subarray(5, 100).filter((b) => b >= 0x80).length);
console.log('all tests pass');
