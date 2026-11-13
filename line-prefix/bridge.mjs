import { createReadStream, createWriteStream } from 'node:fs';
import { readFile } from 'node:fs/promises';
import { pathToFileURL } from 'node:url';

// ABI: UInt32 scalars, little endian. Input and maximum output share one page.
export const MAX_CHUNK = 4096;
export const INPUT_PTR = 0;
export const OUTPUT_PTR = 16384;
const INPUT_HANDLE = 0;
const OUTPUT_HANDLE = 1;
const DATA_CALLBACK = 1;
const CLOSE_CALLBACK = 2;

const scalar = c => Number.isInteger(c) && c >= 0 && c <= 0x10ffff &&
  !(c >= 0xd800 && c <= 0xdfff);

/** Run one instance. Factories are called by Wasm's initialization imports.
 * The reader must supply UTF-8 bytes (setEncoding performs stateful decoding).
 * Resolves on output finish, after accepted writes complete. */
export async function runWithStreams(makeInput, makeOutput, { chunkSize = MAX_CHUNK } = {}) {
  if (!Number.isInteger(chunkSize) || chunkSize < 1 || chunkSize > MAX_CHUNK)
    throw new RangeError('chunkSize must be between 1 and 4096');
  let instance, input, output, ended = false, registeredData = false, registeredClose = false;
  let resolve, reject;
  const completion = new Promise((yes, no) => { resolve = yes; reject = no; });
  // Initialization failures can occur before completion is awaited.
  completion.catch(() => {});
  function fail(error) {
    reject(error);
    input?.destroy();
    output?.destroy();
  }
  function requireInput(handle) {
    if (handle !== INPUT_HANDLE || !input) throw new Error('invalid input handle');
  }
  function requireOutput(handle) {
    if (handle !== OUTPUT_HANDLE || !output) throw new Error('invalid output handle');
  }
  const imports = { bridge: {
    create_input() {
      if (input) throw new Error('input already created');
      input = makeInput();
      input.setEncoding('utf8');
      input.on('error', fail);
      input.on('end', () => { ended = true; });
      return INPUT_HANDLE;
    },
    create_output() {
      if (output) throw new Error('output already created');
      output = makeOutput();
      output.on('error', fail);
      output.on('finish', resolve);
      return OUTPUT_HANDLE;
    },
    on_data(handle, callback) {
      requireInput(handle);
      if (registeredData || callback !== DATA_CALLBACK) throw new Error('invalid data registration');
      registeredData = true;
      input.on('data', text => {
        try {
          const memory = new DataView(instance.exports.memory.buffer);
          let count = 0;
          // JS iteration produces whole code points, never half a surrogate pair.
          for (const character of text) {
            const cp = character.codePointAt(0);
            if (!scalar(cp)) throw new Error('reader delivered an isolated surrogate');
            memory.setUint32(INPUT_PTR + 4 * count++, cp, true);
            if (count === chunkSize) {
              instance.exports.data(count);
              count = 0;
            }
          }
          if (count !== 0) instance.exports.data(count);
        } catch (error) { fail(error); }
      });
    },
    on_close(handle, callback) {
      requireInput(handle);
      if (registeredClose || callback !== CLOSE_CALLBACK) throw new Error('invalid close registration');
      registeredClose = true;
      input.on('close', () => {
        if (!ended) { fail(new Error('input closed before normal end')); return; }
        try { instance.exports.close(); } catch (error) { fail(error); }
      });
    },
    write(handle, pointer, length) {
      requireOutput(handle);
      pointer >>>= 0;
      length >>>= 0;
      const memory = new DataView(instance.exports.memory.buffer);
      if (pointer % 4 !== 0 || pointer + 4 * length > memory.byteLength)
        throw new RangeError('invalid output memory range');
      const codes = new Array(length);
      for (let i = 0; i < length; i++) {
        const cp = memory.getUint32(pointer + 4 * i, true);
        if (!scalar(cp)) throw new Error('Wasm submitted a non-scalar');
        codes[i] = cp;
      }
      // Capture immutable text before returning; later memory reuse is harmless.
      // The maximum 12,288 arguments is bounded by the module's proven ABI.
      output.write(String.fromCodePoint(...codes), 'utf8');
      // Both true and false write returns accept the data. Backpressure is ignored.
    },
    end(handle) {
      requireOutput(handle);
      output.end();
    },
  } };
  const bytes = await readFile(new URL('./prefix.wasm', import.meta.url));
  ({ instance } = await WebAssembly.instantiate(bytes, imports));
  try { instance.exports.init(); } catch (error) { fail(error); }
  await completion;
}

export function prefixFile(inputPath, outputPath, options = {}) {
  return runWithStreams(
    () => createReadStream(inputPath, { highWaterMark: options.highWaterMark ?? 64 * 1024 }),
    () => createWriteStream(outputPath, { encoding: 'utf8' }), options);
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  if (process.argv.length !== 4) {
    console.error('Usage: node bridge.mjs INPUT OUTPUT');
    process.exitCode = 2;
  } else {
    try { await prefixFile(process.argv[2], process.argv[3]); }
    catch (error) { console.error(error.message); process.exitCode = 1; }
  }
}
