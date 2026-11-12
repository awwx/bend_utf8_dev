#!/usr/bin/env bash
# Full check of the Aeneas decoder candidate.  Usage: ./check.sh [--fast]
#   --fast: reuse the pure-layer .olean files in lean/build only if they were
#           built from exactly the current pure-layer sources (sha256 stamp),
#           and run the difftest harness with --no-huge.
# Prints "=== ALL CHECKS PASSED" only if every step succeeded; any failure
# exits non-zero.  What this script does NOT check is printed at the end.
set -euo pipefail
cd "$(dirname "$0")"
HERE=$(pwd)
CAND=$(cd "$HERE/../.." && pwd)        # .../candidates, located from this script's path
export PATH=$HOME/.cargo/bin:$PATH
FAST=${1:-}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
t0=$(date +%s)
step() { echo; echo "=== $* ($(( $(date +%s) - t0 ))s)"; }
fail() { echo "FAIL: $*"; exit 1; }

# Pinned hashes of the two reviewed files.  If either is edited on purpose,
# the reviewer must re-read it and update the hash here.
SPEC_SHA=29396a7e1f013ee5a8cee9b3fb94a186e0f809bd68717f7b3046508cfe3b0583      # spec-lean/Utf8Laws.lean
BOUNDARY_SHA=8666e8c223ee663364b02bba2a06a21f20d3e76dd51d9010aa07cf95a5af33e8  # lean/Boundary.lean
PURE_FILES="Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs"

step "0. reviewed files match their pinned hashes"
echo "$SPEC_SHA  $CAND/spec-lean/Utf8Laws.lean" | sha256sum -c - || fail "spec-lean/Utf8Laws.lean is not the audited spec"
echo "$BOUNDARY_SHA  lean/Boundary.lean" | sha256sum -c - || fail "lean/Boundary.lean differs from the reviewed version"

step "1. spec and pure layer: build copies equal the audited spec / pure-lean sources"
cmp "$CAND/spec-lean/Utf8Laws.lean" "$CAND/pure-lean/Utf8Laws.lean" \
  || fail "pure-lean/Utf8Laws.lean differs from spec-lean/Utf8Laws.lean"
for f in $PURE_FILES; do
  if ! cmp -s "$CAND/pure-lean/$f.lean" "lean/pure/$f.lean"; then
    echo "note: lean/pure/$f.lean was stale; refreshing it from pure-lean/"
    command cp "$CAND/pure-lean/$f.lean" "lean/pure/$f.lean"
  fi
done
# The files the build reads (lean/pure/*) are compared after the refresh with
# the independent sources; the spec copy also with the pinned spec.
for f in $PURE_FILES; do cmp "$CAND/pure-lean/$f.lean" "lean/pure/$f.lean"; done
cmp "$CAND/spec-lean/Utf8Laws.lean" lean/pure/Utf8Laws.lean || fail "build copy of Utf8Laws.lean is not the spec"
echo "lean/pure/*.lean identical to pure-lean/*.lean; Utf8Laws.lean identical to the pinned spec"

step "2. rebuild decoder.wasm (rustc, wasm32-unknown-unknown, release); must equal the shipped file"
cargo build --release --target wasm32-unknown-unknown -j2 > "$T/cargo.log" 2>&1 || { cat "$T/cargo.log"; fail "cargo build"; }
cmp target/wasm32-unknown-unknown/release/decoder.wasm decoder.wasm \
  || fail "shipped decoder.wasm differs from a rebuild of src/lib.rs (copy target/wasm32-unknown-unknown/release/decoder.wasm over it if the source change is intended)"
sha256sum decoder.wasm

step "3. re-run Charon + Aeneas (host and wasm32 targets); compare with lean/Decoder"
./charon.sh "$T/host" > "$T/host.log" 2>&1 || { cat "$T/host.log"; exit 1; }
./charon.sh "$T/wasm" wasm32-unknown-unknown > "$T/wasm.log" 2>&1 || { cat "$T/wasm.log"; exit 1; }
diff -r "$T/host/Decoder" lean/Decoder || fail "regenerated (host) Lean differs from lean/Decoder"
diff -r "$T/wasm/Decoder" lean/Decoder || fail "regenerated (wasm32) Lean differs from lean/Decoder"
if grep -n "sorry" lean/Decoder/*.lean; then fail "Aeneas emitted sorry"; fi
echo "generated Lean identical for host and wasm32 translations"

step "4. forbidden constructs in hand-written Lean"
FORBID='\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|skipKernelTC)\b|#exit|set_option +debug\.'
for f in lean/Boundary.lean lean/Proofs.lean lean/Axioms.lean lean/pure/*.lean; do
  if grep -nE "$FORBID" "$f"; then fail "forbidden construct in $f"; fi
  # bv_decide (native-code axioms): rejected outside comments, as in pure-lean/check.sh
  if grep -nE '^[^-]*\bbv_decide\b' "$f"; then fail "bv_decide in $f"; fi
done
if grep -nE '\b(RefDecoder|Utf8Pure|LoopInv|StRel|PendRel)\b' lean/Boundary.lean; then
  fail "Boundary.lean mentions proof internals"; fi
echo "none (sorry/admit/axiom/native_decide/implemented_by/extern/unsafe/opaque/skipKernelTC/#exit/debug options/bv_decide)"

step "5. build Lean (every error is fatal; candidate .olean files are always rebuilt)"
mkdir -p lean/build
STAMP=lean/build/pure.sha256
PURE_SUM=$( (cd lean/pure && sha256sum $(for f in $PURE_FILES; do echo $f.lean; done)) ; \
            cat "${AENEAS_LEAN:-$HOME/aeneas-nightly/lib/aeneas-lean}/lean-toolchain")
if [ "$FAST" = --fast ] && [ -f "$STAMP" ] && [ "$(cat "$STAMP")" = "$PURE_SUM" ]; then
  echo "(--fast: reusing pure-layer build; stamp matches current sources)"
else
  rm -f "$STAMP" lean/build/Utf8*.olean lean/build/Utf8*.ilean
  lean/build_pure.sh > "$T/pure.log" 2>&1 || { cat "$T/pure.log"; fail "pure layer build"; }
  if grep -n "declaration uses .sorry" "$T/pure.log"; then fail "sorry in pure layer"; fi
  echo "$PURE_SUM" > "$STAMP"
fi
rm -rf lean/build/Decoder lean/build/Boundary.* lean/build/Proofs.*
for f in Decoder/Types.lean Decoder/Funs.lean Boundary.lean Proofs.lean; do
  (cd lean && ./build.sh "$f") > "$T/build.log" 2>&1 || { cat "$T/build.log"; fail "build of lean/$f"; }
  if grep -n "declaration uses .sorry" "$T/build.log"; then fail "sorry in lean/$f"; fi
  echo "built lean/$f"
done

step "6. statement and axioms of the top-level theorem"
cat > "$T/CheckTop.lean" <<'EOF'
import Proofs
-- The theorem named in STATUS.txt has exactly the type of the reviewed claim.
example : Boundary.Verified := DecoderProofs.verified
example : Boundary.Verified = (∃ D : Decoder, D.Correct ∧ Boundary.Realizes D) := rfl
#print axioms DecoderProofs.verified
#print axioms DecoderProofs.realizes
#print axioms Utf8Pure.RefDecoder_correct
EOF
cat > "$T/expected_axioms.txt" <<'EOF'
'DecoderProofs.verified' depends on axioms: [propext, Classical.choice, Quot.sound]
'DecoderProofs.realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Utf8Pure.RefDecoder_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF
L=${AENEAS_LEAN:-$HOME/aeneas-nightly/lib/aeneas-lean}
LP=$(cd "$L" && lake env printenv LEAN_PATH)
(cd lean && LEAN_PATH="$LP:$HERE/lean/build" elan run "$(cat "$L/lean-toolchain")" lean "$T/CheckTop.lean") \
  > "$T/axioms.txt" 2>&1 || { cat "$T/axioms.txt"; fail "top-level statement check"; }
cat "$T/axioms.txt"
diff "$T/expected_axioms.txt" "$T/axioms.txt" || fail "axiom output differs from the expected list"
echo "DecoderProofs.verified : Boundary.Verified; axioms exactly as expected"

step "7. difftest harness (on the shipped decoder.wasm, compared with the rebuild in step 2)"
if [ "$FAST" = --fast ]; then node "$CAND/difftest/run.mjs" "$HERE/decoder.mjs" --no-huge > "$T/dt.log" 2>&1 || { tail -20 "$T/dt.log"; fail difftest; }
else node "$CAND/difftest/run.mjs" "$HERE/decoder.mjs" > "$T/dt.log" 2>&1 || { tail -20 "$T/dt.log"; fail difftest; }; fi
tail -5 "$T/dt.log"
grep -q '^RESULT: PASS' "$T/dt.log" || fail "difftest did not report RESULT: PASS"

cat <<'EOF'

NOT CHECKED by this script (trusted): Charon, Aeneas and its Std model, the Lean
kernel and toolchain versions (not pinned; AENEAS_BIN / AENEAS_LEAN may redirect
them); rustc/LLVM (the release .wasm is built from the same src/lib.rs that Charon
translates in the dev profile; nothing proves the machine code matches the Lean
model); the unsafe shim (mod shim) and the JS wrapper decoder.mjs (exercised only by
the difftest harness); the Wasm engine.
EOF
step "ALL CHECKS PASSED"
