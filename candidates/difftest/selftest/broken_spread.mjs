// BROKEN: argument-count limit.  Converts output with
// String.fromCharCode(...units), which throws RangeError for buffers of
// ~125k units.  Surfaces as an exception (reported under P1), huge corpus only.
import { scan } from '../reference.mjs';
export async function load() {
  return {
    decode_start_state: () => new Uint8Array(0),
    decode_buffer(state, buf) {
      const all = new Uint8Array(state.length + buf.length);
      all.set(state, 0); all.set(buf, state.length);
      const r = scan(all, 0, all.length, false);
      const units = new Array(r.text.length);
      for (let i = 0; i < units.length; i++) units[i] = r.text.charCodeAt(i);
      if (units.length > 100000) throw new RangeError('Maximum call stack size exceeded');  // what the spread does
      const text = String.fromCharCode(...units);
      return [all.slice(r.next), text];
    },
    decode_done: (state) => scan(state, 0, state.length, true).text,
  };
}
