// Sanity checks of the reference itself (hand-written cases from LAWS.bend
// decodes_examples and the chained-vs-from-scratch equivalence).
import { decodeWhole, resolvedPrefix, expectedStream } from './reference.mjs';
import { smallInputs } from './corpus.mjs';
const F = '�';
const ex = [
  [[], ''], [[65,66], 'AB'], [[194,169], '©'], [[194,65], F+'A'], [[192,128], F+F],
  [[194], F], [[194,194,169], F+'©'], [[72,194,169,255], 'H©'+F],
  [[226,130,172], '€'], [[240,159,152,128], '\u{1F600}'], [[226,130], F],
  [[226,130,65], F+'A'], [[240,159,152], F], [[240,159,152,65], F+'A'],
  [[224,128,128], F+F+F], [[237,160,128], F+F+F], [[244,144,128,128], F+F+F+F],
  [[0xEF,0xBB,0xBF,65], '﻿A'],
];
let bad = 0;
for (const [b, s] of ex) { const g = decodeWhole(Uint8Array.from(b)); if (g !== s) { bad++; console.log('FAIL', b, JSON.stringify(g)); } }
console.log(`hand cases: ${ex.length - bad}/${ex.length} ok`);
// chained == from-scratch, and monotone
let n = 0, chainBad = 0;
for (const b of smallInputs(4)) {
  const len = b.length;
  const cuts = []; for (let k = 0; k <= len; k++) cuts.push(k);
  const { outs, done } = expectedStream(b, cuts);
  let acc = '';
  for (let k = 0; k <= len; k++) {
    acc += outs[k];
    if (acc !== resolvedPrefix(b, k)) { chainBad++; console.log('chain mismatch', b, k); }
  }
  if (acc + done !== decodeWhole(b)) { chainBad++; console.log('whole mismatch', b); }
  n++;
}
console.log(`chained vs from-scratch/monotone: ${n} inputs, ${chainBad} problems`);
process.exit(bad || chainBad ? 1 : 0);
