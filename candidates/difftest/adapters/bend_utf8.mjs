// Adapter: /root/bend/utf8/utf8.bend compiled with `bend utf8.bend -o x.mjs`
// (JS target), wrapped to the candidate interface.  Used to cross-check the
// reference against the Bend implementation proved against LAWS.bend.
// The compiled module goes to ../.bend_build/ (nothing in /root/bend/utf8
// is touched).
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync } from 'node:fs';
import { fileURLToPath, pathToFileURL } from 'node:url';
import path from 'node:path';

const here = path.dirname(fileURLToPath(import.meta.url));
const SRC = process.env.BEND_UTF8 || '/root/bend/utf8/utf8.bend';
const OUT = path.join(here, '..', '.bend_build', 'utf8.mjs');

export async function load() {
  if (!existsSync(OUT)) {
    mkdirSync(path.dirname(OUT), { recursive: true });
    const r = spawnSync('bend', [SRC, '-o', OUT], { encoding: 'utf8' });
    if (r.status !== 0) throw new Error(`bend compile failed: ${r.stdout}${r.stderr}`);
  }
  const B = (await import(pathToFileURL(OUT).href)).default;
  const toList = (u8) => {
    let l = { $: 'Nil' };
    for (let i = u8.length - 1; i >= 0; i--) l = { $: 'Con', head: u8[i], tail: l };
    return l;
  };
  return {
    decode_start_state: () => B.decode_start_state(),
    decode_buffer(state, buf) {
      const r = B.decode_buffer(state, toList(buf));   // {$:'Tuple', fst: state, snd: text}
      return [r.fst, r.snd];
    },
    decode_done: (state) => B.decode_done(state),
  };
}
