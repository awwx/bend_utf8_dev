// Property checker: drives a decoder module through the corpus.
import { expectedStream } from './reference.mjs';

const PAD = 3, TAIL = 5;
const ALTS = [[], [0xE2], [0x80], [0xF0, 0x9F], [0xFF], [0x41], [0xC2, 0xA9], [0x82, 0xAC, 0x41]]
  .map((a) => Uint8Array.from(a));

export const hex = (b, max = 48) => {
  const s = Array.from(b.length > max ? b.subarray(0, max) : b, (x) => x.toString(16).padStart(2, '0')).join(' ');
  return b.length > max ? `${s} ...(${b.length} bytes)` : s;
};
const esc = (s) => {
  let o = '';
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    o += c >= 0x20 && c < 0x7F && c !== 0x5C ? s[i] : `\\u${c.toString(16).toUpperCase().padStart(4, '0')}`;
  }
  return o;
};
export function showStr(s, diffAt = 0) {
  if (typeof s !== 'string') return `<${typeof s}: ${String(s)}>`;
  const W = 24;
  if (s.length <= 2 * W) return `"${esc(s)}" (len ${s.length})`;
  const a = Math.max(0, diffAt - W), b = Math.min(s.length, diffAt + W);
  return `${a > 0 ? '...' : ''}"${esc(s.slice(a, b))}"${b < s.length ? '...' : ''} (len ${s.length}, around index ${diffAt})`;
}
const firstDiff = (a, b) => {
  if (typeof a !== 'string' || typeof b !== 'string') return 0;
  const n = Math.min(a.length, b.length);
  let i = 0;
  while (i < n && a.charCodeAt(i) === b.charCodeAt(i)) i++;
  return i;
};

function showChunks(bounds, m) {
  const c = (j) => `[${bounds[j]},${bounds[j + 1]})`;
  if (m <= 10) return Array.from({ length: m }, (_, j) => c(j)).join(' ');
  return `${m} buffers: ${[0, 1, 2, 3].map(c).join(' ')} ... ${[m - 2, m - 1].map(c).join(' ')}`;
}

export class Collector {
  constructor() {
    this.counts = { 1: 0, 2: 0, 3: 0 };
    this.kept = { 1: [], 2: [], 3: [] };
    this.runs = 0; this.calls = 0; this.inputs = 0;
    this.groupFails = 0;
  }
  add(prop, rec) {
    this.counts[prop]++; this.groupFails++;
    const k = this.kept[prop];
    k.push(rec);
    if (k.length > 400) { k.sort((a, b) => a.size - b.size); k.length = 200; }
  }
  minimal(prop, n = 4) {
    return this.kept[prop].slice().sort((a, b) => a.size - b.size).slice(0, n);
  }
}

function makeView(bytes) {
  const backing = new Uint8Array(bytes.length + PAD + TAIL).fill(0xFF);
  backing.set(bytes, PAD);
  return backing;
}
const chunkOf = (backing, a, b) => backing.subarray(PAD + a, PAD + b);

function checkBackingIntact(backing, bytes) {
  for (let i = 0; i < PAD; i++) if (backing[i] !== 0xFF) return `padding byte before the buffer modified (index ${i})`;
  for (let i = 0; i < TAIL; i++) if (backing[PAD + bytes.length + i] !== 0xFF) return `padding byte after the buffer modified (+${i})`;
  for (let i = 0; i < bytes.length; i++) if (backing[PAD + i] !== bytes[i]) return `input byte ${i} modified by decoder`;
  return null;
}

// One call to decode_buffer with shape checking.
function callBuffer(dec, state, buf) {
  const r = dec.decode_buffer(state, buf);
  if (!Array.isArray(r) || r.length !== 2) throw new Error('decode_buffer did not return [state, string]');
  if (typeof r[1] !== 'string') throw new Error(`decode_buffer returned a ${typeof r[1]} instead of a string`);
  return r;
}
function callDone(dec, state) {
  const r = dec.decode_done(state);
  if (typeof r !== 'string') throw new Error(`decode_done returned a ${typeof r} instead of a string`);
  return r;
}

export function runCase(dec, bytes, cuts, ctx, label) {
  const { col } = ctx;
  const n = bytes.length;
  const bounds = [0, ...cuts, n];
  const m = cuts.length + 1;
  const exp = expectedStream(bytes, cuts);
  col.runs++; col.calls += m;
  const fail = (prop, extra) => {
    col.add(prop, { label, hex: hex(bytes), cuts: cuts.join(',') || '(none)', size: n * 64 + m,
      chunks: showChunks(bounds, m), ...extra });
  };

  const backing = makeView(bytes);
  const chunk = (j) => chunkOf(backing, bounds[j], bounds[j + 1]);
  const states = [];
  const outs = [];
  let done, total = '';
  try {
    let s = dec.decode_start_state();
    states.push(s);
    for (let j = 0; j < m; j++) {
      const r = callBuffer(dec, s, chunk(j));
      s = r[0]; outs.push(r[1]); states.push(s);
    }
    done = callDone(dec, s);
  } catch (e) {
    fail(1, { note: `exception after ${outs.length} buffer(s): ${e && e.stack ? e.stack.split('\n').slice(0, 2).join(' | ') : e}` });
    return;
  }
  let ok12 = true;
  // property 2: per-call output
  for (let j = 0; j < m; j++) {
    if (outs[j] !== exp.outs[j]) {
      const d = firstDiff(outs[j], exp.outs[j]);
      fail(2, { note: `buffer #${j} [${bounds[j]},${bounds[j + 1]})`, expected: showStr(exp.outs[j], d), actual: showStr(outs[j], d) });
      ok12 = false; break;
    }
  }
  // property 1: total
  total = outs.join('') + done;
  const expTotal = exp.outs.join('') + exp.done;
  if (total !== expTotal) {
    const d = firstDiff(total, expTotal);
    fail(1, { note: `concatenated output differs${done !== exp.done ? ` (decode_done gave ${showStr(done)}, expected ${showStr(exp.done)})` : ''}`,
      expected: showStr(expTotal, d), actual: showStr(total, d) });
    ok12 = false;
  }

  // ---- property 3: state persistence ------------------------------------
  const bad = checkBackingIntact(backing, bytes);
  if (bad) fail(3, { note: bad });
  try {
    const done2 = callDone(dec, states[m]);
    if (done2 !== done) fail(3, { note: 'decode_done called twice on the same state gave different results', expected: showStr(done), actual: showStr(done2) });
    // Which states to disturb.
    const idxs = [];
    if (ctx.persistAll) for (let i = 0; i <= m; i++) idxs.push(i);
    else if (((ctx.runNo = (ctx.runNo ?? 0) + 1) % (ctx.pokeEvery || 1)) === 0) idxs.push(ctx.runNo % (m + 1));
    for (const i of idxs) persistCheck(dec, states, i, chunk, m, outs, done, ctx, fail);
  } catch (e) {
    fail(3, { note: `exception during persistence check: ${e && e.stack ? e.stack.split('\n').slice(0, 2).join(' | ') : e}` });
  }
}

// Fresh chain: state after buffers 0..i-1, using brand new states.
function freshState(dec, chunk, i) {
  let s = dec.decode_start_state();
  for (let j = 0; j < i; j++) s = callBuffer(dec, s, chunk(j))[0];
  return s;
}

// Use state i for something else (other buffer, done), then check that
// continuing from it behaves exactly as before, and that the side
// calls behave as on a fresh, undisturbed copy of the same state.
function persistCheck(dec, states, i, chunk, m, outs, done, ctx, fail) {
  const alt = ALTS[(ctx.altCounter = (ctx.altCounter ?? 0) + 1) % ALTS.length];
  const si = states[i];
  // reference answers from a fresh chain
  const fr = callBuffer(dec, freshState(dec, chunk, i), alt);
  const frDone = callDone(dec, freshState(dec, chunk, i));
  const frAfterDone = callDone(dec, fr[0]);
  // disturb the shared state
  const r = callBuffer(dec, si, alt);
  const d1 = callDone(dec, si);
  const rDone = callDone(dec, r[0]);
  const where = `state before buffer #${i}${i === m ? ' (final state)' : ''}, disturbed with buffer ${hex(alt)}`;
  if (r[1] !== fr[1] || d1 !== frDone || rDone !== frAfterDone) {
    fail(3, { note: `side calls on a reused state differ from the same calls on a fresh state: ${where}`,
      expected: `buf=${showStr(fr[1])} done=${showStr(frDone)} done-after=${showStr(frAfterDone)}`,
      actual: `buf=${showStr(r[1])} done=${showStr(d1)} done-after=${showStr(rDone)}` });
    return;
  }
  // continue from the disturbed state with the original buffers
  let s = si;
  for (let j = i; j < m; j++) {
    const rr = callBuffer(dec, s, chunk(j));
    s = rr[0];
    if (rr[1] !== outs[j]) {
      fail(3, { note: `after reuse, buffer #${j} gave a different result than the first time: ${where}`,
        expected: showStr(outs[j]), actual: showStr(rr[1]) });
      return;
    }
  }
  const dd = callDone(dec, s);
  if (dd !== done) fail(3, { note: `after reuse, decode_done gave a different result than the first time: ${where}`,
    expected: showStr(done), actual: showStr(dd) });
}

export async function runGroups(dec, groupList, { log = () => {}, maxFailPerGroup = 3000 } = {}) {
  const col = new Collector();
  const perGroup = [];
  for (const g of groupList) {
    const t0 = Date.now();
    const r0 = col.runs, c0 = col.calls;
    col.groupFails = 0;
    const ctx = { col, persistAll: g.persistAll, pokeEvery: g.pokeEvery };
    let inputs = 0, aborted = false;
    outer: for (const item of g.items()) {
      inputs++;
      for (const cuts of item.cutsList) {
        runCase(dec, item.bytes, cuts, ctx, `${g.name}${item.label ? ' / ' + item.label : ''}`);
        if (col.groupFails > maxFailPerGroup) { aborted = true; break outer; }
      }
    }
    col.inputs += inputs;
    const rec = { name: g.name, inputs, runs: col.runs - r0, calls: col.calls - c0, ms: Date.now() - t0, fails: col.groupFails, aborted };
    perGroup.push(rec);
    log(rec);
  }
  return { col, perGroup };
}
