// BROKEN: ignores the Uint8Array's byteOffset/length (uses buf.buffer),
// a classic wrapper bug when the caller passes a subarray.
import { scan } from '../reference.mjs';
export async function load() {
  return {
    decode_start_state: () => new Uint8Array(0),
    decode_buffer(state, buf) {
      const raw = new Uint8Array(buf.buffer);
      const all = new Uint8Array(state.length + raw.length);
      all.set(state, 0); all.set(raw, state.length);
      const r = scan(all, 0, all.length, false);
      return [all.slice(r.next), r.text];
    },
    decode_done: (state) => scan(state, 0, state.length, true).text,
  };
}
