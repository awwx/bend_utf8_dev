import { createReadStream, createWriteStream } from 'node:fs';
import { readFile } from 'node:fs/promises';
import { pathToFileURL } from 'node:url';

// ABI: strings cross as externrefs; Wasm uses the native js-string builtins.
// The chunk limit counts UTF-16 code units, not Unicode scalars.
export const MAX_CHUNK = 4096;
const INPUT_HANDLE = 0;
const OUTPUT_HANDLE = 1;
const DATA_CALLBACK = 1;
const CLOSE_CALLBACK = 2;

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
          // Only inspect potential split boundaries; no per-character copying.
          // A size-one request still delivers a surrogate pair together.
          for (let start = 0; start < text.length;) {
            let end = Math.min(start + chunkSize, text.length);
            if (end < text.length) {
              const last = text.charCodeAt(end - 1);
              const next = text.charCodeAt(end);
              if (last >= 0xd800 && last <= 0xdbff && next >= 0xdc00 && next <= 0xdfff)
                end += end - start === 1 ? 1 : -1;
            }
            const chunk = text.slice(start, end);
            instance.exports.data(chunk, chunk.length);
            start = end;
          }
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
    write(handle, text) {
      requireOutput(handle);
      if (typeof text !== 'string') throw new TypeError('Wasm submitted a non-string');
      // fromCharCodeArray has already captured an immutable JavaScript string.
      // Both true and false write returns accept it. Backpressure is ignored.
      output.write(text, 'utf8');
    },
    end(handle) {
      requireOutput(handle);
      output.end();
    },
  } };
  const bytes = await readFile(new URL('./prefix.wasm', import.meta.url));
  ({ instance } = await WebAssembly.instantiate(bytes, imports, { builtins: ['js-string'] }));
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
