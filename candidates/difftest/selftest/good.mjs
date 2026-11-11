// Trivially correct adapter built from the reference.  State = immutable
// Uint8Array of the held-back (incomplete but completable) bytes.
import { scan } from '../reference.mjs';
export async function load() {
  return {
    decode_start_state: () => new Uint8Array(0),
    decode_buffer(state, buf) {
      const all = new Uint8Array(state.length + buf.length);
      all.set(state, 0); all.set(buf, state.length);
      const r = scan(all, 0, all.length, false);
      return [all.slice(r.next), r.text];
    },
    decode_done: (state) => scan(state, 0, state.length, true).text,
  };
}
