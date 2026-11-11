// usage: node run.mjs <path-to-decoder.mjs> [--quick] [--no-huge] [--max-len N] [--fails N]
import { pathToFileURL } from 'node:url';
import path from 'node:path';
import { groups } from './corpus.mjs';
import { runGroups } from './harness.mjs';

const args = process.argv.slice(2);
const file = args.find((a) => !a.startsWith('--') && isNaN(a));
const opt = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
if (!file) { console.error('usage: node run.mjs <decoder.mjs> [--quick] [--no-huge] [--max-len N] [--only substr] [--fails N]'); process.exit(2); }
const quick = args.includes('--quick');
const maxExhaustive = opt('--max-len') !== undefined ? Number(opt('--max-len')) : quick ? 4 : 6;
const nShow = Number(opt('--fails') ?? 3);

const t0 = Date.now();
const mod = await import(pathToFileURL(path.resolve(file)).href);
const dec = await mod.load();
for (const f of ['decode_start_state', 'decode_buffer', 'decode_done'])
  if (typeof dec[f] !== 'function') { console.error(`load() result lacks function ${f}`); process.exit(2); }
console.log(`decoder: ${file}`);
const only = opt('--only');
const glist = groups({ maxExhaustive, noHuge: quick || args.includes('--no-huge') }).filter((g) => !only || g.name.includes(only));
const { col, perGroup } = await runGroups(dec, glist, {
  log: (g) => console.log(`  ${String(g.ms).padStart(6)} ms  ${String(g.runs).padStart(9)} runs ${String(g.calls).padStart(10)} calls  ${g.fails ? 'FAILS=' + g.fails + (g.aborted ? ' (group aborted)' : '') : 'ok'}  ${g.name}`),
});
const names = { 1: 'P1 total output', 2: 'P2 per-call output (safe and prompt)', 3: 'P3 state persistence / buffer hygiene' };
console.log(`\ninputs ${col.inputs}, (input,split) runs ${col.runs}, decode_buffer calls ${col.calls}, ${((Date.now() - t0) / 1000).toFixed(1)} s`);
let failed = false;
for (const p of [1, 2, 3]) {
  const c = col.counts[p];
  console.log(`${names[p]}: ${c === 0 ? 'PASS' : 'FAIL (' + c + ' failing runs)'}`);
  if (c) failed = true;
}
for (const p of [1, 2, 3]) {
  const ex = col.minimal(p, nShow);
  if (!ex.length) continue;
  console.log(`\n--- first minimal failures, ${names[p]} ---`);
  for (const f of ex) {
    console.log(`group:    ${f.label}\ninput:    ${f.hex}\nsplit:    ${f.chunks}\nnote:     ${f.note ?? ''}`);
    if (f.expected !== undefined) console.log(`expected: ${f.expected}\nactual:   ${f.actual}`);
    console.log('');
  }
}
console.log(failed ? 'RESULT: FAIL' : 'RESULT: PASS');
process.exit(failed ? 1 : 0);
