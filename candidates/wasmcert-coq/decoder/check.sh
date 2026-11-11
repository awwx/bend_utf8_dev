#!/bin/sh
# Build everything against the REAL pure layer, print decoder.wasm from the
# Rocq term (Binary.v also proves the parse-back check by vm_compute),
# reject proof holes, print assumptions, run the difftest harness.
set -e
cd "$(dirname "$0")"
eval $(opam env --switch=wasmcert) 2>/dev/null
test -f ../../pure-rocq/Utf8Proofs.vo || { echo "FAIL: real pure layer not built (run ../../pure-rocq/check.sh)"; exit 1; }
echo "== build (time)"
time make all
echo "== decoder.wasm from the term (parse-back lemma decoder_bytes_parse_back is in Binary.v)"
command rm -f decoder.wasm decoder_hex.out
make decoder.wasm
ls -l decoder.wasm
echo "== checking for holes"
if grep -nwE 'Admitted|admit|Axiom|Parameter|Abort' $(sed -n 's/^\([A-Za-z]*\.v\)$/\1/p' _CoqProject); then
  echo "FAIL: proof holes found"; exit 1
fi
echo "no Admitted/admit/Axiom/Parameter/Abort in the build files"
echo "== Print Assumptions"
rocq c -Q . Decoder -Q ../../pure-rocq Utf8 Assumptions.v 2>&1 | grep -v 'Running as root'
echo "== difftest harness"
node ../../difftest/run.mjs ./decoder.mjs
