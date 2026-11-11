// BROKEN: a sequence truncated at end of input gives one U+FFFD per byte
// instead of one per maximal subpart.  Violates P1 (and nothing per-call).
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
    decode_done: (state) => '�'.repeat(state.length),
  };
}
