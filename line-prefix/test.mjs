import assert from 'node:assert/strict';
import { Readable, Writable } from 'node:stream';
import { constants as bufferConstants } from 'node:buffer';
import { mkdtemp, writeFile, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runWithStreams, prefixFile } from './bridge.mjs';

// Exercise boundaries of Wasm's internal slices, not bridge-created chunks.
const MAX_CHUNK = 4096;
assert(bufferConstants.MAX_STRING_LENGTH < 2 ** 32,
  'native strings must fit the proved unsigned-i32 length interface');

function expected(text) {
  const chars = Array.from(text);
  return chars.map((c, i) => (i === 0 || chars[i - 1] === '\n' ? '> ' : '') + c).join('');
}
// Confirm that the shipped module imports the native string builtins, and
// that enabling them removes those imports from the JS linking interface.
const wasmBytes = await readFile(new URL('./prefix.wasm', import.meta.url));
const rawModule = new WebAssembly.Module(wasmBytes);
assert.deepEqual(WebAssembly.Module.imports(rawModule)
  .filter(i => i.module === 'wasm:js-string').map(i => i.name).sort(),
  ['charCodeAt', 'fromCharCodeArray', 'intoCharCodeArray', 'length', 'substring']);
const builtinModule = new WebAssembly.Module(wasmBytes, { builtins: ['js-string'] });
assert(WebAssembly.Module.imports(builtinModule).every(i => i.module === 'bridge'));
assert(!WebAssembly.Module.exports(builtinModule).some(e => e.kind === 'memory'));

// Direct public-callback checks exercise explicit empty deliveries and one
// large string, without allowing the bridge to pre-split or compute its length.
const directWrites = [];
let directClosed = false;
const direct = await WebAssembly.instantiate(builtinModule, { bridge: {
  create_input: () => 0, create_output: () => 1,
  on_data: (h, cb) => { assert.equal(h, 0); assert.equal(cb, 1); },
  on_close: (h, cb) => { assert.equal(h, 0); assert.equal(cb, 2); },
  write: (h, text) => {
    assert.equal(h, 1);
    assert(text.isWellFormed(), 'each write must contain complete characters');
    assert(text.length <= 3 * MAX_CHUNK, 'output slices must stay bounded');
    directWrites.push(text);
  },
  end: h => { assert.equal(h, 1); directClosed = true; },
} });
assert.equal(direct.exports.data.length, 1, 'only a string crosses the public ABI');
direct.exports.init();
direct.exports.data('');
assert.equal(directWrites.length, 0, 'empty delivery must not produce a write');
direct.exports.data('start\n');
const beforeEmpty = directWrites.length;
direct.exports.data('');
assert.equal(directWrites.length, beforeEmpty);
const largeDelivery = 'a'.repeat(MAX_CHUNK - 1) + '😀\n' + '\n'.repeat(10000);
direct.exports.data(largeDelivery);
assert(directWrites.length > beforeEmpty + 1, 'Wasm must split a large event');
assert.equal(directWrites.join(''), expected('start\n' + largeDelivery));
direct.exports.close();
assert(directClosed);

let cases = 0;
async function check(text, buffers) {
  const accepted = [];
  let finished = false;
  await runWithStreams(() => Readable.from(buffers), () => {
    const writer = new Writable({
      highWaterMark: 1, // Make write(false) common; acceptance must still be FIFO.
      write(bytes, encoding, done) {
        // Defer completion beyond the callback and subsequent GC-array allocations.
        setImmediate(() => { accepted.push(Buffer.from(bytes)); done(); });
      },
    });
    writer.on('finish', () => { finished = true; });
    return writer;
  });
  assert(finished, 'must wait for output completion');
  assert.deepEqual(Buffer.concat(accepted), Buffer.from(expected(text)),
    `mismatch for ${JSON.stringify(text.slice(0, 80))}`);
  cases++;
}
const examples = ['', 'hello', 'hello\n', 'hello\nworld', '\n', '\n\n',
  'a\n\nb', 'a\r\nb', '\0\r', '😀\n𝄞é\n', '\n😀\n', '\uFEFFhello',
  String.fromCodePoint(0xd7ff, 0xe000, 0x10ffff)];
for (const text of examples) {
  const bytes = Buffer.from(text);
  await check(text, bytes.length ? [bytes] : []);
  for (let cut = 1; cut < bytes.length; cut++)
    await check(text, [bytes.subarray(0, cut), bytes.subarray(cut)]);
  await check(text, Array.from(bytes, byte => Buffer.from([byte])));
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
  await check(small, buffers);
}
// Worst expansion exactly fills the output array; persistent line state crosses chunks.
for (const text of ['\n'.repeat(MAX_CHUNK * 2 + 1),
    'a'.repeat(MAX_CHUNK - 1) + '\n😀tail\n', 'a'.repeat(MAX_CHUNK * 2 + 1),
    'a'.repeat(MAX_CHUNK - 1) + '😀\n𝄞tail',
    '😀'.repeat(MAX_CHUNK + 1)])
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
  await prefixFile(join(dir, 'in'), join(dir, 'out'), { highWaterMark: 1 });
  assert.deepEqual(await readFile(join(dir, 'out')), Buffer.from(expected(text)));
} finally { await rm(dir, { recursive: true, force: true }); }
console.log(`PASS: ${cases} stream cases, all Unicode scalars, real-file byte-split test, and direct full-string callback checks`);
