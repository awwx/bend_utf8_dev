// Test corpus.  Each group is {name, items: () => iterator of
// {bytes: Uint8Array, cutsList: number[][], label?}}.
// A "cuts" array is a non-decreasing list of interior split points in
// [0, n]; the buffers are bytes[0,c1) bytes[c1,c2) ... bytes[ck,n).
// Equal cut points, or cuts at 0 / n, give empty buffers.

export const ALPHABET = [0x00, 0x41, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF,
  0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1, 0xEC, 0xED, 0xEE, 0xEF,
  0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xFF];
// Smaller alphabet (one or two representatives of each byte class and
// each boundary that matters) for longer exhaustive lengths.
export const ALPHABET_5 = [0x41, 0x80, 0x8F, 0x90, 0xBF, 0xC2, 0xE0, 0xED, 0xF0, 0xF4];
export const ALPHABET_6 = [0x41, 0x80, 0xA0, 0xC2, 0xE0, 0xF0];

// ---- cut enumerators -------------------------------------------------

// all non-decreasing sequences over 0..n of length <= n+1 (includes
// empty buffers anywhere)
function cutsAllMonotone(n) {
  const out = [];
  const rec = (cur, min) => {
    out.push(cur.slice());
    if (cur.length >= n + 1) return;
    for (let c = min; c <= n; c++) { cur.push(c); rec(cur, c); cur.pop(); }
  };
  rec([], 0);
  return out;
}
// every subset of the interior positions 1..n-1 (all splits into
// non-empty consecutive buffers); variants add an empty buffer at the
// start and/or end.
function cutsSubsets(n, variants) {
  const out = [];
  const m = Math.max(0, n - 1);
  for (let mask = 0; mask < (1 << m); mask++) {
    const base = [];
    for (let i = 0; i < m; i++) if (mask & (1 << i)) base.push(i + 1);
    out.push(base);
    if (variants) {
      out.push([0, ...base]);
      out.push([...base, n]);
      out.push([0, ...base, n]);
    }
  }
  return out;
}

const cache = new Map();
function memo(key, f) { if (!cache.has(key)) cache.set(key, f()); return cache.get(key); }

// ---- exhaustive ------------------------------------------------------

export function* allSequences(alphabet, len) {
  const idx = new Array(len).fill(0);
  const total = alphabet.length ** len;
  for (let t = 0; t < total; t++) {
    const b = new Uint8Array(len);
    for (let i = 0; i < len; i++) b[i] = alphabet[idx[i]];
    yield b;
    for (let i = len - 1; i >= 0; i--) { if (++idx[i] < alphabet.length) break; idx[i] = 0; }
  }
}
export function* smallInputs(maxLen) {
  for (let n = 0; n <= maxLen; n++) yield* allSequences(ALPHABET, n);
}

// Exhaustive group definitions: [length, alphabet, cut-style]
export const EXHAUSTIVE = [
  { n: 0, alpha: ALPHABET, style: 'all' },
  { n: 1, alpha: ALPHABET, style: 'all' },
  { n: 2, alpha: ALPHABET, style: 'all' },
  { n: 3, alpha: ALPHABET, style: 'subsets+ends' },
  { n: 4, alpha: ALPHABET, style: 'subsets' },
  { n: 5, alpha: ALPHABET_5, style: 'subsets' },
  { n: 6, alpha: ALPHABET_6, style: 'subsets' },
];
function exhaustiveGroup({ n, alpha, style }) {
  return {
    name: `exhaustive len=${n} alphabet=${alpha.length} cuts=${style}`,
    persistAll: n <= 2,
    pokeEvery: n >= 4 ? 4 : 1,
    *items() {
      const cutsList = memo(`${n}${style}`, () =>
        style === 'all' ? cutsAllMonotone(n) : cutsSubsets(n, style === 'subsets+ends'));
      for (const bytes of allSequences(alpha, n)) yield { bytes, cutsList };
    },
  };
}

// ---- scalar boundaries -----------------------------------------------

// Encoding by the generic UTF-8 bit layout, for any value up to 0x1FFFFF
// (so surrogates and > 10FFFF can be written).  minLen forces overlong.
export function encodeGeneric(cp, minLen = 1) {
  let len = cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4;
  if (minLen > len) len = minLen;
  if (len === 1) return [cp];
  const out = new Array(len);
  for (let i = len - 1; i >= 1; i--) { out[i] = 0x80 | (cp & 0x3F); cp >>= 6; }
  out[0] = ([0, 0, 0xC0, 0xE0, 0xF0])[len] | cp;
  return out;
}

export function scalarBoundaryEncodings() {
  const base = [0x0, 0x7F, 0x80, 0x7FF, 0x800, 0xFFF, 0x1000, 0xCFFF, 0xD000,
    0xD7FF, 0xD800, 0xDBFF, 0xDC00, 0xDFFF, 0xE000, 0xFFFD, 0xFFFE, 0xFFFF,
    0x10000, 0x3FFFF, 0x40000, 0xFFFFF, 0x100000, 0x10FFFF, 0x110000, 0x13FFFF,
    0x1FFFFF, 0xFEFF];
  const cps = new Set();
  for (const c of base) for (const d of [-1, 0, 1]) if (c + d >= 0) cps.add(c + d);
  const encs = [];
  for (const cp of [...cps].sort((a, b) => a - b)) {
    encs.push({ label: `U+${cp.toString(16)}`, bytes: encodeGeneric(cp) });
    // overlong forms
    for (const ml of [2, 3, 4]) {
      const e = encodeGeneric(cp, ml);
      if (e.length === ml && encodeGeneric(cp).length < ml) encs.push({ label: `U+${cp.toString(16)} overlong${ml}`, bytes: e });
    }
  }
  return encs;
}

function boundaryGroup() {
  return {
    name: 'scalar-boundaries (+truncations, contexts, pairs)',
    persistAll: false,
    *items() {
      const encs = scalarBoundaryEncodings();
      const subsets = (n) => memo(`bs${n}`, () => cutsSubsets(n, true));
      const emit = (label, arr, ends = true) => ({ label, bytes: Uint8Array.from(arr),
        cutsList: ends ? subsets(arr.length) : memo(`bn${arr.length}`, () => cutsSubsets(arr.length, false)) });
      for (const e of encs) {
        const b = e.bytes;
        yield emit(e.label, b);
        for (let k = 1; k < b.length; k++) {
          yield emit(`${e.label} trunc${k}`, b.slice(0, k));
          for (const nxt of [0x41, 0x80, 0xC2, 0xE2, 0xF0, 0xFF])
            yield emit(`${e.label} trunc${k} +${nxt.toString(16)}`, [...b.slice(0, k), nxt]);
        }
        yield emit(`A ${e.label}`, [0x41, ...b]);
        yield emit(`${e.label} A`, [...b, 0x41]);
        yield emit(`${e.label} 80`, [...b, 0x80]);
        yield emit(`${e.label} BF`, [...b, 0xBF]);
        yield emit(`${e.label} ${e.label}`, [...b, ...b]);
      }
      // pairs of well-formed boundary encodings (and ill-formed ones)
      for (const a of encs) for (const b of encs) {
        if (a.bytes.length + b.bytes.length > 7) continue;
        yield emit(`${a.label} ${b.label}`, [...a.bytes, ...b.bytes], false);
      }
    },
  };
}

// ---- random ----------------------------------------------------------

export function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// valid UTF-8 for random scalars (mixture of lengths), ~n bytes
export function randomValid(rng, n) {
  const out = new Uint8Array(n + 4);
  let p = 0;
  while (p < n) {
    const r = rng();
    let cp;
    if (r < 0.45) cp = Math.floor(rng() * 0x80);
    else if (r < 0.65) cp = 0x80 + Math.floor(rng() * (0x800 - 0x80));
    else if (r < 0.9) { do cp = 0x800 + Math.floor(rng() * (0x10000 - 0x800)); while (cp >= 0xD800 && cp < 0xE000); }
    else cp = 0x10000 + Math.floor(rng() * (0x110000 - 0x10000));
    const e = encodeGeneric(cp);
    for (const x of e) out[p++] = x;
  }
  return out.subarray(0, p);
}

// corrupt: per-byte probability `rate` of drop / replace / insert with a
// boundary byte; optionally chop up to 3 bytes off the end.
export function corrupt(rng, src, rate) {
  const out = new Uint8Array(src.length * 2 + 8);
  let p = 0;
  const pick = () => ALPHABET[Math.floor(rng() * ALPHABET.length)];
  for (let i = 0; i < src.length; i++) {
    if (rng() < rate) {
      const op = Math.floor(rng() * 3);
      if (op === 0) continue;
      if (op === 1) { out[p++] = pick(); continue; }
      out[p++] = pick();
    }
    out[p++] = src[i];
  }
  if (rng() < 0.5) p = Math.max(0, p - Math.floor(rng() * 4));
  return out.slice(0, p);
}

function randomCuts(rng, n, style) {
  const cuts = [];
  if (style === 'few') {
    const k = Math.floor(rng() * 6);
    for (let i = 0; i < k; i++) cuts.push(Math.floor(rng() * (n + 1)));
  } else if (style === 'many') {
    const k = 1 + Math.floor(rng() * Math.min(300, n + 1));
    for (let i = 0; i < k; i++) cuts.push(Math.floor(rng() * (n + 1)));
  } else if (style === 'bytewise-head') {
    for (let i = 0; i <= Math.min(n, 64); i++) cuts.push(i);
  } else if (style === 'chunks') {          // random chunk sizes 0..40
    let c = 0;
    while (c < n) { c += Math.floor(rng() * 41); if (c < n) cuts.push(c); }
  }
  cuts.sort((a, b) => a - b);
  return cuts;
}

function randomGroup(seed, count, maxLen, rate) {
  return {
    name: `random seed=${seed} count=${count} maxLen=${maxLen} corruption=${rate}`,
    persistAll: false,
    *items() {
      const rng = mulberry32(seed);
      for (let t = 0; t < count; t++) {
        const n = Math.floor(rng() * maxLen);
        let bytes = randomValid(rng, n);
        const r = rate === 'mixed' ? [0, 0.002, 0.02, 0.2][t & 3] : rate;
        if (r > 0) bytes = corrupt(rng, bytes, r);
        const cutsList = ['few', 'many', 'bytewise-head', 'chunks'].map((s) => randomCuts(rng, bytes.length, s));
        yield { bytes, cutsList, label: `rand#${t}` };
      }
    },
  };
}

function randomLongGroup() {
  return {
    name: 'random long (100KB..1MB), seed=777',
    persistAll: false,
    *items() {
      const rng = mulberry32(777);
      for (let t = 0; t < 10; t++) {
        const n = 100000 + Math.floor(rng() * 900000);
        let bytes = randomValid(rng, n);
        bytes = corrupt(rng, bytes, [0, 0.0005, 0.01, 0][t % 4]);
        const cutsList = [randomCuts(rng, bytes.length, 'few'), randomCuts(rng, bytes.length, 'many'),
          randomCuts(rng, bytes.length, 'bytewise-head')];
        // many mid-sized chunks
        const big = []; for (let c = 0; c < bytes.length; c += 1 + Math.floor(rng() * 5000)) big.push(c);
        cutsList.push(big);
        yield { bytes, cutsList, label: `long#${t}` };
      }
    },
  };
}

// Multi-megabyte buffers, usually delivered in a single call, to expose
// argument-count limits (String.fromCharCode(...arr), push(...arr)) and
// fixed-size scratch buffers.
function hugeGroup() {
  const MB = 1 << 20;
  return {
    name: 'huge buffers (multi-MB in one call, seed=4242)',
    persistAll: false,
    *items() {
      const rng = mulberry32(4242);
      const fill = (n, f) => { const b = new Uint8Array(n); for (let i = 0; i < n; i++) b[i] = f(i); return b; };
      const cases = [];
      cases.push(['ascii 8MB', fill(8 * MB, (i) => 0x20 + (i % 95))]);
      cases.push(['all-0xFF 3MB (3M replacement chars)', fill(3 * MB, () => 0xFF)]);
      cases.push(['U+1F600 x 1M (4MB)', fill(4 * MB, (i) => [0xF0, 0x9F, 0x98, 0x80][i & 3])]);
      cases.push(['U+20AC x 1.5M (4.5MB)', fill(4.5 * MB, (i) => [0xE2, 0x82, 0xAC][i % 3])]);
      cases.push(['U+00E9 x 2M (4MB)', fill(4 * MB, (i) => [0xC3, 0xA9][i & 1])]);
      cases.push(['truncated 4-byte seqs F0 9F 98 repeated 3MB', fill(3 * MB, (i) => [0xF0, 0x9F, 0x98][i % 3])]);
      cases.push(['random valid mixed 6MB', randomValid(rng, 6 * MB)]);
      cases.push(['random mixed corrupted 5MB', corrupt(rng, randomValid(rng, 5 * MB), 0.01)]);
      cases.push(['random heavily corrupted 3MB', corrupt(rng, randomValid(rng, 3 * MB), 0.3)]);
      for (const [label, bytes] of cases) {
        const n = bytes.length;
        const mid = Math.floor(n / 2);
        yield {
          bytes, label,
          cutsList: [[], [0], [mid], [n], [mid - 1, mid, mid + 1], [n - 3, n - 2, n - 1], [1, 2, 3]],
        };
      }
      // huge text that ends in an incomplete sequence, one-call and split
      const t = new Uint8Array(5 * MB + 2); t.fill(0x41); t[t.length - 2] = 0xE2; t[t.length - 1] = 0x82;
      yield { bytes: t, label: 'ascii 5MB + E2 82', cutsList: [[], [t.length - 1], [5 * MB]] };
    },
  };
}

export function groups(opts = {}) {
  const maxN = opts.maxExhaustive ?? 6;
  const g = EXHAUSTIVE.filter((e) => e.n <= maxN).map(exhaustiveGroup);
  g.push(boundaryGroup());
  g.push(randomGroup(1, 600, 3000, 'mixed'));
  g.push(randomGroup(2, 100, 40, 'mixed'));
  g.push(randomLongGroup());
  if (!opts.noHuge) g.push(hugeGroup());
  return g;
}
