difftest: black-box differential tests for streaming UTF-8 decoder wrappers
===========================================================================

Candidate interface (candidates/<name>/decoder.mjs):
  export async function load()  ->  { decode_start_state, decode_buffer, decode_done }
  decode_start_state() -> state
  decode_buffer(state, Uint8Array) -> [state, string]
  decode_done(state) -> string

Run (Node 26, no dependencies):
  node run.mjs <path-to-decoder.mjs>            full corpus (see runtimes below)
  node run.mjs <decoder.mjs> --quick            exhaustive up to length 4, no huge buffers
  node run.mjs <decoder.mjs> --no-huge          full corpus except the multi-MB buffers
  node run.mjs <decoder.mjs> --max-len N        exhaustive lengths 0..N (N <= 6)
  node run.mjs <decoder.mjs> --only <substr>    only corpus groups whose name contains substr
  node run.mjs <decoder.mjs> --fails N          show N minimal failures per property (default 3)
Exit status 0 = all pass, 1 = some property failed, 2 = usage / load error.

Self-test (the harness must pass the good adapter and catch the broken ones):
  node selftest/run.mjs            (about 1 minute)
Reference sanity checks:
  node refcheck.mjs                      hand cases from LAWS.bend decodes_examples,
                                         and chained-vs-from-scratch prefix equivalence
  node crosscheck_textdecoder.mjs [--max-len N] [--huge]
                                         reference vs Node TextDecoder('utf-8',{ignoreBOM:true}),
                                         whole-buffer and {stream:true} per chunk
  node run.mjs adapters/bend_utf8.mjs    the Bend implementation (/root/bend/utf8/utf8.bend,
                                         compiled by `bend ... -o .bend_build/utf8.mjs`) through
                                         the full harness

Files
  reference.mjs   non-streaming reference written from the Unicode table (scan(), decodeWhole,
                  resolvedPrefix, expectedStream).  Independent of every candidate.
  corpus.mjs      corpus groups (below)
  harness.mjs     the property checks; run.mjs the CLI
  selftest/       good.mjs (built from the reference), broken_holdall / broken_perbyte /
                  broken_mutable / broken_offset / broken_spread
  adapters/       bend_utf8.mjs (Bend JS target wrapped to the interface)

Properties
  Expected values come from reference.mjs only.  For an input and a split into buffers:
  P1 Total.   concatenation of all decode_buffer strings + decode_done == decodeWhole(input).
              (Exceptions thrown by the decoder, wrong return shapes and non-string results are
              also reported under P1.)
  P2 Per call (safe and prompt).  The string returned by call k equals the new part of
              resolvedPrefix(bytes so far): the reference decoding of everything seen with a trailing
              incomplete-but-completable sequence held back.  Checked call by call, so both
              emitting too early (unsafe) and too late (not prompt) fail.
  P3 State persistence and buffer hygiene.  For one or more of the states seen in each run
              (all states for lengths <= 2, otherwise a rotating sample; every 4th run in the
              length >= 4 exhaustive groups), the harness: calls decode_buffer on that state with a
              different "alien" buffer, calls decode_done on it, then replays the original
              remaining buffers from the same state and checks the replay equals the first run.
              The side calls are compared with the same calls on a freshly rebuilt, undisturbed
              state, so P3 failures are separated from P1/P2 bugs.  Also: decode_done twice on
              the final state gives the same text; the caller's input buffers are not modified
              (and neither is the 0xFF padding around them).
  Buffers are passed as subarray views of a larger Uint8Array (non-zero byteOffset, surrounding
  bytes 0xFF), so wrappers that use buf.buffer, or read outside the view, are caught.

Corpus (default full run; counts as run against selftest/good.mjs)
  exhaustive, alphabet 00 41 7F 80 8F 90 9F A0 BF C0 C1 C2 DF E0 E1 EC ED EE EF F0 F1 F3 F4 F5 FF:
    len 0,1,2: every split incl. empty buffers anywhere (all non-decreasing cut lists)
    len 3: every split into consecutive buffers, plus empty first/last buffer variants
    len 4: every split into consecutive non-empty buffers (3.1M runs)
    len 5: 10-byte alphabet, len 6: 6-byte alphabet (1.6M and 1.5M runs), every split
  scalar boundaries: encodings (also surrogates, > 10FFFF, overlongs) of the boundary scalars
    0 7F 80 7FF 800 FFF 1000 CFFF D000 D7FF D800 DBFF DC00 DFFF E000 FEFF FFFD FFFE FFFF 10000
    3FFFF 40000 FFFFF 100000 10FFFF 110000 ... and each +-1; all truncations, with a following
    41/80/C2/E2/F0/FF, in context, doubled, and pairs; every split
  random (seeded mulberry32): 600 inputs up to 3000 bytes + 100 short ones (valid text with
    0..20% corruption), 4 split styles each; 10 inputs of 100KB..1MB (splits incl. byte-wise head)
  huge: ten inputs of 3..8 MB (ASCII, all-FF, all-4-byte, all-3-byte, truncated sequences,
    random valid, corrupted) in a single call, halves, three-way splits, split near ends
Totals for the full run: 564,671 inputs, 6.93M (input,split) runs, 20.6M decode_buffer calls.
Runtime is dominated by the candidate: selftest/good.mjs about 55 s alone; the Bend JS build
  (adapters/bend_utf8.mjs) about 1.5 min without the huge group, plus about 9 min for the huge
  group (lists of millions of nodes, plus the persistence replays).  Use --no-huge / --quick
  for fast iterations; a wasm candidate should be much closer to the good adapter.
Cross-check runtimes: crosscheck_textdecoder.mjs --max-len 6 --huge about 36 s.

Known limitations / judgement calls
  - "every split" is exhaustive only for lengths <= 6 over reduced alphabets; empty buffers in
    the middle are exhaustive only up to length 2.
  - P2 is stated as "equals reference prefix minus held-back trailing sequence"; this is the
    longest text all continuations agree on, since a held-back sequence is exactly a proper
    prefix of a well-formed sequence (a continuation can complete it) and any other trailing
    subpart has already been decided.
  - A candidate state may be any JS value; the harness never inspects it.
