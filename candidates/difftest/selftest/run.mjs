// Runs the harness against the good adapter (must pass) and each broken
// adapter (must fail the property named in its EXPECT entry).
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
const dir = path.dirname(fileURLToPath(import.meta.url));
const runner = path.join(dir, '..', 'run.mjs');
const full = process.argv.includes('--full');
const cases = [
  ['good.mjs', []],
  ['broken_holdall.mjs', [2]],
  ['broken_perbyte.mjs', [1]],
  ['broken_mutable.mjs', [3]],
  ['broken_offset.mjs', [1, 2]],
  ['broken_spread.mjs', [1]],         // needs the huge corpus
];
let bad = 0;
for (const [f, expectFail] of cases) {
  const args = [runner, path.join(dir, f), '--fails', '1'];
  if (f === 'broken_spread.mjs') args.push('--only', 'huge');
  else if (!full) args.push('--max-len', '4', '--no-huge');
  const r = spawnSync('node', args, { encoding: 'utf8', maxBuffer: 1 << 28 });
  const out = r.stdout;
  const got = [1, 2, 3].filter((p) => new RegExp(`^P${p} .*: FAIL`, 'm').test(out));
  const okExpected = expectFail.every((p) => got.includes(p)) && (expectFail.length === 0 ? got.length === 0 : true);
  const exactOnly = expectFail.length === 0 || got.every((p) => expectFail.includes(p));
  const good = okExpected && exactOnly && (r.status === (expectFail.length ? 1 : 0));
  console.log(`${good ? 'OK ' : 'BAD'} ${f}: expected failing [${expectFail}] got failing [${got}] exit ${r.status}`);
  const first = out.split('\n').find((l) => l.startsWith('note:'));
  const ex = out.split('\n').filter((l) => /^(input|split|expected|actual):/.test(l)).slice(0, 4);
  if (expectFail.length) console.log('      first failure: ' + [first, ...ex].filter(Boolean).join('\n                     '));
  if (!good) bad++;
}
process.exit(bad ? 1 : 0);
