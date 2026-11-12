#!/usr/bin/env bash
# Check of the Talos decoder candidate.  The candidate is PARTIAL: the top-level
# claim Utf8Boundary.ShippedModuleCorrect (Boundary.lean) is NOT proved; see
# STATUS.txt.  This script checks what exists and ends with a "PARTIAL:" line;
# it never prints an unqualified pass line.  Any failing step exits non-zero.
#
# Steps: pinned hashes of the reviewed files; the shipped decoder.wasm equals a
# rebuild from decoder.wat and its `wasm-tools print` text equals
# decoder.printed.wat (the text Boundary.lean / DecoderModule.lean include);
# spec / pure-layer copies; forbidden constructs; clean Lean build; statements
# and axioms of the proved partial results; difftest on the shipped bytes.
#
# Depends on (not built here): the Talos checkout built in ../talos (see
# ../SETUP.md) and wasm-tools in ../tools.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
CAND=$(cd "$here/../.." && pwd)
WT=$CAND/talos/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools
TALOS=$CAND/talos/talos/interpreter
PURE=$CAND/pure-lean
SPEC=$CAND/spec-lean/Utf8Laws.lean
TC=$(cat lean-toolchain)
LEANC="elan run $TC lean"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "FAIL: $*"; exit 1; }

SPEC_SHA=29396a7e1f013ee5a8cee9b3fb94a186e0f809bd68717f7b3046508cfe3b0583      # spec-lean/Utf8Laws.lean
BOUNDARY_SHA=e84440bc9cabde9d84fa5835a0caaec2c4a5a56e84a0d8d54c051be7a3e1ab57  # Boundary.lean

echo "== dependencies"
[ -x "$WT" ] || fail "wasm-tools not found at $WT (see ../SETUP.md)"
[ -d "$TALOS/.lake/build" ] || fail "Talos interpreter not built in $TALOS (see ../SETUP.md)"
[ "$(cat "$TALOS/lean-toolchain")" = "$TC" ] || fail "Talos toolchain $(cat "$TALOS/lean-toolchain") != $TC"
echo "wasm-tools $($WT --version); Talos at $TALOS; Lean $TC"

echo "== reviewed files match their pinned hashes"
echo "$SPEC_SHA  $SPEC" | sha256sum -c - || fail "spec-lean/Utf8Laws.lean is not the audited spec"
echo "$BOUNDARY_SHA  Boundary.lean" | sha256sum -c - || fail "Boundary.lean differs from the reviewed version"

echo "== wasm: shipped bytes = rebuild from decoder.wat; printed text = decoder.printed.wat"
$WT parse decoder.wat -o "$T/unstripped.wasm"
$WT strip --all -o "$T/rebuilt.wasm" "$T/unstripped.wasm"
cmp "$T/rebuilt.wasm" decoder.wasm || fail "shipped decoder.wasm differs from a rebuild of decoder.wat"
$WT validate decoder.wasm
$WT print decoder.wasm > "$T/printed.wat"
cmp decoder.printed.wat "$T/printed.wat" || { diff decoder.printed.wat "$T/printed.wat" || true; fail "decoder.printed.wat is not the printed text of the shipped decoder.wasm"; }
sha256sum decoder.wasm decoder.printed.wat

echo "== spec and pure layer copies"
cmp "$SPEC" "$PURE/Utf8Laws.lean" || fail "pure-lean/Utf8Laws.lean differs from the spec"
for f in Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs; do
  if ! cmp -s "$PURE/$f.lean" "$f.lean"; then
    echo "note: $f.lean was stale; refreshing it from pure-lean/"; command cp "$PURE/$f.lean" "$f.lean"; fi
  cmp "$PURE/$f.lean" "$f.lean"
done
cmp "$SPEC" Utf8Laws.lean || fail "build copy Utf8Laws.lean is not the spec"
echo "copies identical to pure-lean/; Utf8Laws.lean identical to the pinned spec"

OURS="DecoderModule Boundary ProofMach ProofFuncs ProofStep ProofLoop ProofBuffer ProofDone ProofModel Axioms"
echo "== forbidden constructs"
FORBID='\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|skipKernelTC)\b|#exit|set_option +debug\.'
for f in $OURS Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs; do
  if grep -nE "$FORBID" "$f.lean"; then fail "forbidden construct in $f.lean"; fi
  # bv_decide (native-code axioms): rejected outside comments, as in pure-lean/check.sh
  if grep -nE '^[^-]*\bbv_decide\b' "$f.lean"; then fail "bv_decide in $f.lean"; fi
done
echo "none"

echo "== lean (clean build; every error is fatal)"
export LEAN_PATH=$(cd "$TALOS" && lake env printenv LEAN_PATH):$here/build
rm -rf build; mkdir -p build
for f in Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs DecoderModule Boundary ProofMach ProofFuncs \
         ProofStep ProofLoop ProofBuffer ProofDone ProofModel; do
  s=$(date +%s)
  $LEANC -o "build/$f.olean" "$here/$f.lean" > "$T/$f.log" 2>&1 || { cat "$T/$f.log"; fail "build of $f.lean"; }
  if grep -n "declaration uses .sorry" "$T/$f.log"; then fail "sorry in $f.lean"; fi
  echo "$f.lean: $(( $(date +%s) - s )) s"
done

echo "== statements and axioms of the proved partial results"
# Types are compared with the text recorded when STATUS.txt was written, so a
# weakened statement fails.  (Definitions they use, e.g. runM / stepM / Rel in
# the proof files, are not pinned.)
{ echo "import ProofBuffer"; echo "import ProofDone"; echo "import ProofModel"; echo "import Utf8Proofs"
  echo "set_option pp.oneline false"
  echo "example : Utf8Boundary.printedWat = Utf8Wasm.printedWat := rfl"
  for t in Utf8Wasm.decoderModule_decodes Utf8Wasm.start_ok Utf8Wasm.done_runs Utf8Wasm.buffer_runs \
           Utf8Wasm.call_step Utf8Wasm.loop_correct Utf8Wasm.stepM_nil Utf8Pure.RefDecoder_correct; do
    echo "#check @$t"; echo "#print axioms $t"; done; } > "$T/CheckPartial.lean"
$LEANC "$T/CheckPartial.lean" > "$T/partial.txt" 2>&1 || { cat "$T/partial.txt"; fail "statement check"; }
cat "$T/partial.txt"
# check.expected.txt holds the output recorded for the statements in STATUS.txt.
diff check.expected.txt "$T/partial.txt" || fail "statements or axioms of the partial results differ from check.expected.txt"
if grep -q sorryAx "$T/partial.txt"; then fail "sorryAx"; fi
echo "statements as recorded; every result depends only on [propext, Classical.choice, Quot.sound]"

echo "== difftest (on the shipped decoder.wasm checked above)"
node "$CAND/difftest/run.mjs" "$here/decoder.mjs" > "$T/dt.log" 2>&1 || { tail -20 "$T/dt.log"; fail difftest; }
tail -5 "$T/dt.log"
grep -q '^RESULT: PASS' "$T/dt.log" || fail "difftest did not report RESULT: PASS"

cat <<'EOF'

NOT CHECKED (trusted or not proved): the top-level claim ShippedModuleCorrect
(not proved: per-byte model refinement for 1-3 pending bytes, runM/memory-layout
lemmas, assembly, the 2^32 edge case; see STATUS.txt); wasm-tools print/parse
(the theorem is about the module Talos decodes from the printed text, not about
the bytes); Talos's semantics and decoder, instantiation and validation (not
modelled); the JS wrapper decoder.mjs and the Wasm engine (exercised only by the
difftest harness).
EOF
echo "PARTIAL: checks above passed (shipped wasm = rebuild, printed text matches, clean build, statements and axioms as recorded, difftest PASS); top-level theorem Utf8Boundary.ShippedModuleCorrect NOT proved"
