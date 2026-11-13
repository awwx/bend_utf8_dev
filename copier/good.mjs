// For the purposes of this demo we ignore errors and backpressure.

import { createReadStream, createWriteStream } from 'node:fs';
import process from 'node:process';

const input = createReadStream('in.txt', {encoding: 'utf8'});
const output = createWriteStream('out.txt', {encoding: 'utf8'});

input.on('data', (text) => {
  output.write(text);
});

input.on('close', () => {
  output.close();
});
