import { createReadStream, createWriteStream } from 'node:fs';
import process from 'node:process';

const input = createReadStream('in.txt', {encoding: 'utf8'});
const output = createWriteStream('out.txt', {encoding: 'utf8'});

function failfast(e) {
  console.error(e);
  process.exit(1);
}

input.on('error', failfast);
output.on('error', failfast);

input.on('data', (text) => {
  // This demo ignores backpressure; queued writes may use lots of memory.
  output.write(text);
});

input.on('close', () => {
  output.close();
});
