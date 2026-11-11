// Cross-check reference.mjs against Node's TextDecoder('utf-8', {ignoreBOM: true}):
//  (a) whole-buffer decode, (b) per-chunk output with {stream: true}.
// usage: node crosscheck_textdecoder.mjs [--max-len N] [--huge]
import { groups } from './corpus.mjs';
import { decodeWhole, expectedStream } from './reference.mjs';
import { hex, showStr } from './harness.mjs';

const args = process.argv.slice(2);
const mi = args.indexOf('--max-len');
const maxExhaustive = mi >= 0 ? Number(args[mi + 1]) : 5;
const huge = args.includes('--huge');
const mk = () => new TextDecoder('utf-8', { ignoreBOM: true });

let whole = 0, wholeBad = 0, runs = 0, streamBad = 0, doneBad = 0;
const exWhole = [], exStream = [];
const seenWhole = new Set();
const t0 = Date.now();
for (const g of groups({ maxExhaustive, noHuge: !huge })) {
  for (const item of g.items()) {
    const b = item.bytes;
    whole++;
    const want = decodeWhole(b), got = mk().decode(b);
    if (want !== got) { wholeBad++; if (exWhole.length < 5) exWhole.push({ g: g.name, hex: hex(b), want: showStr(want), got: showStr(got) }); }
    if (b.length > 100000 && !huge) continue;
    for (const cuts of item.cutsList) {
      runs++;
      const exp = expectedStream(b, cuts);
      const td = mk();
      const bounds = [0, ...cuts, b.length];
      let bad = null;
      for (let j = 0; j + 1 < bounds.length; j++) {
        const out = td.decode(b.subarray(bounds[j], bounds[j + 1]), { stream: true });
        if (out !== exp.outs[j]) { bad = { j, want: exp.outs[j], got: out }; streamBad++; break; }
      }
      if (!bad) {
        const d = td.decode();
        if (d !== exp.done) { doneBad++; bad = { j: 'done', want: exp.done, got: d }; }
      }
      if (bad && (exStream.length < 400)) exStream.push({ size: b.length * 64 + cuts.length, g: g.name, hex: hex(b), cuts: cuts.join(',') || '(none)', ...bad });
    }
  }
}
console.log(`inputs ${whole}, split runs ${runs}, ${((Date.now() - t0) / 1000).toFixed(1)} s`);
console.log(`whole-buffer: ${wholeBad} disagreements with TextDecoder`);
for (const e of exWhole) console.log('  ', JSON.stringify(e));
console.log(`stream:true per-chunk: ${streamBad} runs disagree on a chunk; ${doneBad} runs agree on chunks but disagree on the final flush`);
exStream.sort((a, b) => a.size - b.size);
for (const e of exStream.slice(0, 8)) console.log(`   input ${e.hex} cuts ${e.cuts} buffer#${e.j}: reference ${showStr(e.want)} TextDecoder ${showStr(e.got)}`);
process.exit(wholeBad || streamBad || doneBad ? 1 : 0);
