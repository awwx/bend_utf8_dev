// Simple, non-streaming reference for UTF-8 decoding with the Unicode
// "maximal subpart" replacement rule, no BOM handling.
//
// Table of well-formed sequences (Unicode Table 3-7):
//   00..7F
//   C2..DF  80..BF
//   E0      A0..BF 80..BF
//   E1..EC  80..BF 80..BF
//   ED      80..9F 80..BF
//   EE..EF  80..BF 80..BF
//   F0      90..BF 80..BF 80..BF
//   F1..F3  80..BF 80..BF 80..BF
//   F4      80..8F 80..BF 80..BF
// Every other byte (80..C1, F5..FF) cannot start a sequence: one U+FFFD.

// -> null for a byte that cannot begin a sequence, else
//    {total: sequence length, lo, hi: allowed range of the 2nd byte}
function leadInfo(b) {
  if (b >= 0xC2 && b <= 0xDF) return { total: 2, lo: 0x80, hi: 0xBF };
  if (b === 0xE0) return { total: 3, lo: 0xA0, hi: 0xBF };
  if (b >= 0xE1 && b <= 0xEC) return { total: 3, lo: 0x80, hi: 0xBF };
  if (b === 0xED) return { total: 3, lo: 0x80, hi: 0x9F };
  if (b === 0xEE || b === 0xEF) return { total: 3, lo: 0x80, hi: 0xBF };
  if (b === 0xF0) return { total: 4, lo: 0x90, hi: 0xBF };
  if (b >= 0xF1 && b <= 0xF3) return { total: 4, lo: 0x80, hi: 0xBF };
  if (b === 0xF4) return { total: 4, lo: 0x80, hi: 0x8F };
  return null;
}

function unitsToString(units, n) {
  if (n < 24) { let r = ''; for (let i = 0; i < n; i++) r += String.fromCharCode(units[i]); return r; }
  const parts = [];
  for (let i = 0; i < n; i += 8192) {
    parts.push(String.fromCharCode.apply(null, units.subarray(i, Math.min(n, i + 8192))));
  }
  return parts.join('');
}

// Decode bytes[start, end).  Returns {text, next}: `next` is the index
// of the first byte not consumed.  With final=false, a trailing
// sequence that is a proper prefix of a well-formed one (it ran out of
// input while every byte so far was still allowed) is held back:
// next < end in that case.  With final=true that sequence is one U+FFFD
// and next === end.
export function scan(bytes, start, end, final) {
  const units = new Uint16Array(end - start + 1);
  let n = 0;
  let i = start;
  while (i < end) {
    const b = bytes[i];
    if (b < 0x80) { units[n++] = b; i += 1; continue; }
    const info = leadInfo(b);
    if (info === null) { units[n++] = 0xFFFD; i += 1; continue; }
    let cp = b & (0xFF >> (info.total + 1));
    let j = 1;
    let status = 'ok';
    while (j < info.total) {
      if (i + j >= end) { status = 'incomplete'; break; }
      const c = bytes[i + j];
      const lo = j === 1 ? info.lo : 0x80;
      const hi = j === 1 ? info.hi : 0xBF;
      if (c < lo || c > hi) { status = 'bad'; break; }
      cp = (cp << 6) | (c & 0x3F);
      j++;
    }
    if (status === 'ok') {
      if (cp >= 0x10000) {
        const v = cp - 0x10000;
        units[n++] = 0xD800 + (v >> 10);
        units[n++] = 0xDC00 + (v & 0x3FF);
      } else units[n++] = cp;
      i += j;
    } else if (status === 'bad') {
      units[n++] = 0xFFFD; i += j;      // j bytes form the maximal subpart
    } else if (final) {
      units[n++] = 0xFFFD; i += j;
    } else {
      break;                            // held back
    }
  }
  return { text: unitsToString(units, n), next: i };
}

// Whole-buffer decode (end of input).
export function decodeWhole(bytes) { return scan(bytes, 0, bytes.length, true).text; }

// Text that is final after seeing exactly bytes[0, k): everything except a
// trailing incomplete-but-completable sequence.
export function resolvedPrefix(bytes, k) { return scan(bytes, 0, k, false).text; }

// Expected per-call outputs for the given interior cut points
// (non-decreasing).  Returns {outs: string[] (one per buffer), done: string}.
// Chained: each call resumes at the held-back position of the previous.
export function expectedStream(bytes, cuts) {
  const bounds = [...cuts, bytes.length];
  const outs = [];
  let next = 0;
  for (const c of bounds) {
    const r = scan(bytes, next, c, false);
    outs.push(r.text);
    next = r.next;
  }
  const done = scan(bytes, next, bytes.length, true).text;
  return { outs, done };
}
