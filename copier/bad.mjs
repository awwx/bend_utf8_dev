// This demo ignores backpressure; queued writes may use lots of memory.

import { createReadStream, createWriteStream } from 'node:fs';
import process from 'node:process';

const input = createReadStream('in.txt');
const output = createWriteStream('out.txt');

function failfast(e) {
  console.error(e);
  process.exit(1);
}

input.on('error', failfast);
output.on('error', failfast);

input.on('data', (buffer) => {
  const text = buffer.toString('utf8');
  output.write(text);
});

input.on('close', () => {
  output.close();
});
