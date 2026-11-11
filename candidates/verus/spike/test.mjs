import assert from 'node:assert/strict';
import { is_surrogate_code_point as s, count_non_ascii as c } from './spike.mjs';
for (const [cp, e] of [[0,false],[0xD7FF,false],[0xD800,true],[0xDC00,true],[0xDFFF,true],[0xE000,false],[0xFFFFFFFF,false]])
  assert.equal(s(cp), e, cp.toString(16));
assert.equal(c(new Uint8Array([])), 0);
assert.equal(c(new Uint8Array([0x41,0x7f,0x80,0xff,0xc3,0xa9])), 4);
assert.equal(c(new Uint8Array(100000).fill(0x80)), 100000); // forces memory.grow
assert.equal(c(new TextEncoder().encode('héllo €😀')), 2+3+4 );
// exhaustive vs naive for all surrogate boundaries of u32 samples
for (let cp = 0; cp < 0x120000; cp += 1) assert.equal(s(cp), cp >= 0xD800 && cp <= 0xDFFF);
console.log('all JS tests pass');
