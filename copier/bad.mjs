// For the purposes of this demo we ignore errors and backpressure.

import { createReadStream, createWriteStream } from 'node:fs';
import process from 'node:process';

const input = createReadStream('in.txt');
const output = createWriteStream('out.txt');

input.on('data', (buffer) => {
  const text = buffer.toString('utf8');
  output.write(text);
});

input.on('close', () => {
  output.close();
});
