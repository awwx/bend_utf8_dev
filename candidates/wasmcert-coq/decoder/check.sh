#!/usr/bin/env bash
# Check of the WasmCert-Coq decoder candidate.  The candidate is PARTIAL: the
# top-level claim decoder_module_correct (Boundary.v) is proved only
# CONDITIONALLY, as decoder_module_correct_if_step : (forall hs, step_spec hs)
# -> decoder_module_correct, and step_spec is not proved (see STATUS.txt).
# This script checks what exists and ends with a "PARTIAL:" line; it never
# prints an unqualified pass line.  Any failing step exits non-zero.
#
# Depends on (not built here; it fails if out of date): the real pure layer in
# ../../pure-rocq, built by ../../pure-rocq/check.sh (about 9 min).
set -euo pipefail
cd "$(dirname "$0")"
HERE=$(pwd)
CAND=$(cd "$HERE/../.." && pwd)
PURE=$CAND/pure-rocq
SPEC=$CAND/spec-rocq/Utf8Laws.v
eval "$(opam env --switch=wasmcert 2>/dev/null)"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "FAIL: $*"; exit 1; }

SPEC_SHA=e5d72692cbe154feb46891bb914c6ee62dc27474ca2d6598afee99313f49eb75      # spec-rocq/Utf8Laws.v
BOUNDARY_SHA=65cc3b6a066d36b01cdc7883c17c5d2923819f22e0669ac9cc681d8af130c6d6  # Boundary.v

echo "== reviewed files match their pinned hashes"
echo "$SPEC_SHA  $SPEC" | sha256sum -c - || fail "spec-rocq/Utf8Laws.v is not the audited spec"
echo "$BOUNDARY_SHA  Boundary.v" | sha256sum -c - || fail "Boundary.v differs from the reviewed version"

echo "== pure layer ../../pure-rocq: spec copy and build are current"
cmp "$SPEC" "$PURE/Utf8Laws.v" || fail "pure-rocq/Utf8Laws.v differs from the spec"
for f in $(sed -n 's/^\([A-Za-z0-9_]*\)\.v$/\1/p' "$PURE/_CoqProject"); do
  [ -f "$PURE/$f.vo" ] || fail "pure-rocq/$f.vo missing: run $PURE/check.sh first"
  [ "$PURE/$f.vo" -nt "$PURE/$f.v" ] || fail "pure-rocq/$f.vo older than $f.v: run $PURE/check.sh first"
done
echo "pure-rocq .vo files present and newer than their sources (hole check: Print Assumptions below is transitive)"

echo "== checking for holes in the candidate's build files"
VFILES=$(sed -n 's/^\([A-Za-z0-9_]*\.v\)$/\1/p' _CoqProject)
if grep -nwE 'Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture|Abort' $VFILES; then
  fail "proof holes found"; fi
if grep -nE 'Unset +(Guard|Positivity|Universe) +Checking|Bypass|Admit +Obligations' $VFILES; then
  fail "checker-weakening command found"; fi
echo "no Admitted/admit/Axiom/Parameter/Conjecture/Abort/Unset ... Checking in: $VFILES"

echo "== build (clean: candidate .vo files are always rebuilt, so no stale artefact counts)"
for f in $VFILES EmitHex.v Assumptions.v; do b=${f%.v}; command rm -f "$b.vo" "$b.vok" "$b.vos" "$b.glob" ".$b.aux"; done
make all > "$T/make.log" 2>&1 || { cat "$T/make.log"; fail "make all"; }
grep -E '^ROCQ compile' "$T/make.log" | tr '\n' ' '; echo

echo "== decoder.wasm regenerated from the term must equal the shipped file"
command cp decoder.wasm "$T/shipped.wasm"
# decoder_hex.out is an intermediate (tracked for reference); regenerated below.
[ -f decoder_hex.out ] && command cp decoder_hex.out "$T/shipped_hex.out" || : > "$T/shipped_hex.out"
command rm -f decoder.wasm decoder_hex.out
if ! make decoder.wasm > "$T/emit.log" 2>&1; then
  cat "$T/emit.log"; command cp "$T/shipped.wasm" decoder.wasm; command cp "$T/shipped_hex.out" decoder_hex.out
  fail "make decoder.wasm"; fi
if ! cmp decoder.wasm "$T/shipped.wasm"; then
  command mv decoder.wasm decoder.wasm.regenerated
  command cp "$T/shipped.wasm" decoder.wasm; command cp "$T/shipped_hex.out" decoder_hex.out
  fail "shipped decoder.wasm differs from the bytes printed from decoder_module (kept as decoder.wasm.regenerated)"
fi
sha256sum decoder.wasm
echo "identical (Binary.v also proves decoder_bytes_parse_back: run_parse_module decoder_bytes = Some decoder_module)"

echo "== statements and assumptions"
# check.expected.txt holds the recorded output: the type of the conditional
# theorem, the definition of step_spec (so it cannot be made unsatisfiable,
# e.g. False, unnoticed), the decoder_bytes link, and every Print Assumptions.
cat > "$T/CheckTop.v" <<'EOV'
From Decoder Require Import Boundary Binary Exports Decode Theorems.
Check decoder_module_correct_if_step.
Check decoder_bytes_parse_back.
Print decoder_bytes.
Print step_spec.
Print Assumptions decoder_module_correct_if_step.
Print Assumptions decoder_bytes_parse_back.
Print Assumptions start_correct.
Print Assumptions done_correct.
Print Assumptions decode_correct.
EOV
rocq c -Q . Decoder -Q "$PURE" Utf8 "$T/CheckTop.v" > "$T/assum.raw" 2>&1 || { cat "$T/assum.raw"; fail "statement check"; }
grep -v 'Running as root' "$T/assum.raw" > "$T/assum.txt" || true
cat "$T/assum.txt"
diff check.expected.txt "$T/assum.txt" || fail "statements or assumptions differ from check.expected.txt"
echo "statements, step_spec and assumptions as recorded"

echo "== difftest harness (on the shipped decoder.wasm checked above)"
node "$CAND/difftest/run.mjs" "$HERE/decoder.mjs" > "$T/dt.log" 2>&1 || { tail -20 "$T/dt.log"; fail difftest; }
tail -5 "$T/dt.log"
grep -q '^RESULT: PASS' "$T/dt.log" || fail "difftest did not report RESULT: PASS"

cat <<'EOF'

NOT CHECKED (trusted or not proved): step_spec (not proved; the top-level claim is
conditional on it); determinism of the semantics (not proved, so "reduces to this
result" does not exclude another, trapping, reduction); WasmCert-Coq's semantics,
its binary printer binary_of_module (the parser direction is checked by
decoder_bytes_parse_back) and its library axioms (listed above); the hex-to-bytes
step in the Makefile (node); the JS wrapper decoder.mjs and the Wasm engine
(exercised only by the difftest harness).
EOF
echo "PARTIAL: checks above passed (shipped wasm = bytes printed from the term, build, statements and assumptions as recorded, difftest PASS); decoder_module_correct proved only conditionally on the unproved step_spec"
