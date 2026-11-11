#!/usr/bin/env bash
# Rebuild decoder.wasm from decoder.wat, re-derive the text the Lean proofs
# read from the shipped bytes, check the copied spec / pure layer, build all
# Lean files, reject sorry/axiom/native_decide, print axioms, run difftest.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
WT=$here/../tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools
PURE=$here/../../pure-lean
SPEC=$here/../../spec-lean/Utf8Laws.lean

echo "== wasm"
$WT parse decoder.wat -o decoder.unstripped.wasm
$WT strip --all -o decoder.wasm decoder.unstripped.wasm
rm -f decoder.unstripped.wasm
$WT validate decoder.wasm
$WT print decoder.wasm > decoder.printed.wat.new
if ! cmp -s decoder.printed.wat decoder.printed.wat.new; then
  echo "FAIL: decoder.printed.wat is stale"; diff decoder.printed.wat decoder.printed.wat.new || true; exit 1
fi
rm -f decoder.printed.wat.new
sha256sum decoder.wasm decoder.printed.wat

echo "== spec and pure layer copies (unmodified)"
for f in Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs; do
  command cp "$PURE/$f.lean" "$f.lean"
  cmp "$PURE/$f.lean" "$f.lean"
done
cmp "$SPEC" Utf8Laws.lean
echo "byte-identical"

OURS="DecoderModule Boundary ProofMach ProofFuncs ProofStep ProofLoop ProofBuffer ProofDone ProofModel Axioms"
echo "== forbidden constructs"
for f in $OURS; do
  if grep -nE '\b(sorry|admit|axiom|native_decide|bv_decide|implemented_by|extern)\b' "$f.lean"; then
    echo "FAIL: forbidden construct in $f.lean"; exit 1
  fi
done
echo "none"

echo "== lean (Lean $(lean --version | head -1))"
export LEAN_PATH=$(cd ../talos/interpreter && lake env printenv LEAN_PATH):$here/build
mkdir -p build
for f in Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs DecoderModule Boundary ProofMach ProofFuncs \
         ProofStep ProofLoop ProofBuffer ProofDone ProofModel; do
  s=$(date +%s)
  lean -o "build/$f.olean" "$here/$f.lean" 2>&1 | grep -E 'error' && { echo "FAIL in $f"; exit 1; }
  echo "$f.lean: $(( $(date +%s) - s )) s"
done
lean "$here/Axioms.lean" 2>&1 | tee build/axioms.txt
if grep -q sorryAx build/axioms.txt; then echo "FAIL: sorryAx"; exit 1; fi
BAD=$(tr -d '\n' < build/axioms.txt | grep -o '\[[^]]*\]' | tr -d '[] ' | tr ',' '\n' \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)
if [ -n "$BAD" ]; then echo "FAIL: unexpected axioms: $BAD"; exit 1; fi

echo "== difftest"
node ../../difftest/run.mjs "$here/decoder.mjs"
echo "CHECK PASSED (see STATUS.txt for what is and is not proved)"
