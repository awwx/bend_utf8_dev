import assert from 'node:assert/strict';
import { Readable, Writable } from 'node:stream';
import { mkdtemp, writeFile, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runWithStreams, prefixFile, MAX_CHUNK } from './bridge.mjs';

function expected(text) {
  const chars = Array.from(text);
  return chars.map((c, i) => (i === 0 || chars[i - 1] === '\n' ? '> ' : '') + c).join('');
}
let cases = 0;
async function check(text, buffers, chunkSize = MAX_CHUNK) {
  const accepted = [];
  let finished = false;
  await runWithStreams(() => Readable.from(buffers), () => {
    const writer = new Writable({
      highWaterMark: 1, // Make write(false) common; acceptance must still be FIFO.
      write(bytes, encoding, done) {
        // Defer completion until after Wasm has reused its output buffer.
        setImmediate(() => { accepted.push(Buffer.from(bytes)); done(); });
      },
    });
    writer.on('finish', () => { finished = true; });
    return writer;
  }, { chunkSize });
  assert(finished, 'must wait for output completion');
  assert.deepEqual(Buffer.concat(accepted), Buffer.from(expected(text)),
    `mismatch for ${JSON.stringify(text.slice(0, 80))}, chunk ${chunkSize}`);
  cases++;
}
const examples = ['', 'hello', 'hello\n', 'hello\nworld', '\n', '\n\n',
  'a\n\nb', 'a\r\nb', '\0\r', '😀\n𝄞é\n', '\n😀\n', '\uFEFFhello',
  String.fromCodePoint(0xd7ff, 0xe000, 0x10ffff)];
for (const text of examples) {
  const bytes = Buffer.from(text);
  for (const chunkSize of [1, 2, 7, MAX_CHUNK]) {
    await check(text, bytes.length ? [bytes] : [], chunkSize);
    for (let cut = 1; cut < bytes.length; cut++)
      await check(text, [bytes.subarray(0, cut), bytes.subarray(cut)], chunkSize);
    await check(text, Array.from(bytes, byte => Buffer.from([byte])), chunkSize);
  }
}
// Every raw partition of a string with a four-byte scalar and an LF.
const small = '😀\nx';
const smallBytes = Buffer.from(small);
for (let mask = 0; mask < 1 << (smallBytes.length - 1); mask++) {
  const buffers = [];
  let start = 0;
  for (let i = 1; i < smallBytes.length; i++) {
    if (mask & (1 << (i - 1))) { buffers.push(smallBytes.subarray(start, i)); start = i; }
  }
  buffers.push(smallBytes.subarray(start));
  await check(small, buffers, 2);
}
// Worst expansion exactly fills the output region; persistent line state crosses chunks.
for (const text of ['\n'.repeat(MAX_CHUNK * 2 + 1),
    'a'.repeat(MAX_CHUNK - 1) + '\n😀tail\n', 'a'.repeat(MAX_CHUNK * 2 + 1)])
  await check(text, [Buffer.from(text)]);
// Exercise every Unicode scalar, including supplementary characters.
const blocks = [];
for (let lo = 0; lo <= 0x10ffff; lo += 2048) {
  const cps = [];
  for (let cp = lo; cp < Math.min(lo + 2048, 0x110000); cp++)
    if (cp < 0xd800 || cp > 0xdfff) cps.push(cp);
  blocks.push(String.fromCodePoint(...cps));
}
const allScalars = blocks.join('');
await check(allScalars, [Buffer.from(allScalars)]);

const dir = await mkdtemp(join(tmpdir(), 'line-prefix-'));
try {
  const text = '😀\r\n\nlast\n';
  await writeFile(join(dir, 'in'), text);
  await prefixFile(join(dir, 'in'), join(dir, 'out'), { highWaterMark: 1, chunkSize: 2 });
  assert.deepEqual(await readFile(join(dir, 'out')), Buffer.from(expected(text)));
} finally { await rm(dir, { recursive: true, force: true }); }
console.log(`PASS: ${cases} stream cases, all Unicode scalars, and real-file byte-split test`);
