// BROKEN: hidden mutable state.  The state object is updated in place
// and returned, so a state value is not usable after it has been passed
// to decode_buffer.  Passes P1/P2 for ordinary use; violates P3.
import { scan } from '../reference.mjs';
export async function load() {
  return {
    decode_start_state: () => ({ held: new Uint8Array(0) }),
    decode_buffer(state, buf) {
      const all = new Uint8Array(state.held.length + buf.length);
      all.set(state.held, 0); all.set(buf, state.held.length);
      const r = scan(all, 0, all.length, false);
      state.held = all.slice(r.next);
      return [state, r.text];
    },
    decode_done: (state) => scan(state.held, 0, state.held.length, true).text,
  };
}
