// BROKEN: keeps every byte and returns all text from decode_done only.
// Violates P2 (prompt output); P1 total is fine.
import { scan } from '../reference.mjs';
export async function load() {
  return {
    decode_start_state: () => new Uint8Array(0),
    decode_buffer(state, buf) {
      const all = new Uint8Array(state.length + buf.length);
      all.set(state, 0); all.set(buf, state.length);
      return [all, ''];
    },
    decode_done: (state) => scan(state, 0, state.length, true).text,
  };
}
