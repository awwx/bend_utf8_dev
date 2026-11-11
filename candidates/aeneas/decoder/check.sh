#!/usr/bin/env bash
# Full check of the Aeneas decoder candidate.  Usage: ./check.sh [--fast]
#   --fast: reuse the pure-layer .olean files in lean/build if present (saves ~4-5 min)
#           and run the difftest harness with --no-huge.
set -euo pipefail
cd "$(dirname "$0")"
HERE=$(pwd)
export PATH=$HOME/.cargo/bin:$PATH
FAST=${1:-}
CAND=$HERE/../..
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
t0=$(date +%s)
step() { echo; echo "=== $* ($(( $(date +%s) - t0 ))s)"; }

step "1. spec and pure layer are unmodified copies"
command cp "$CAND/spec-lean/Utf8Laws.lean" lean/pure/Utf8Laws.lean
cmp "$CAND/spec-lean/Utf8Laws.lean" lean/pure/Utf8Laws.lean
cmp "$CAND/pure-lean/Utf8Laws.lean" lean/pure/Utf8Laws.lean
for f in Utf8Bits Utf8Ref Utf8Table Utf8Proofs; do
  command cp "$CAND/pure-lean/$f.lean" lean/pure/$f.lean
  cmp "$CAND/pure-lean/$f.lean" lean/pure/$f.lean
done
echo "byte-identical"

step "2. build decoder.wasm (rustc, wasm32-unknown-unknown, release)"
cargo build --release --target wasm32-unknown-unknown -j2 2>&1 | tail -1
command cp target/wasm32-unknown-unknown/release/decoder.wasm decoder.wasm
ls -l decoder.wasm

step "3. re-run Charon + Aeneas (host and wasm32 targets); compare with lean/Decoder"
./charon.sh "$T/host" > "$T/host.log" 2>&1 || { cat "$T/host.log"; exit 1; }
./charon.sh "$T/wasm" wasm32-unknown-unknown > "$T/wasm.log" 2>&1 || { cat "$T/wasm.log"; exit 1; }
diff -r "$T/host/Decoder" lean/Decoder || { echo "FAIL: regenerated (host) Lean differs from lean/Decoder"; exit 1; }
diff -r "$T/wasm/Decoder" lean/Decoder || { echo "FAIL: regenerated (wasm32) Lean differs from lean/Decoder"; exit 1; }
if grep -n "sorry" lean/Decoder/*.lean; then echo "FAIL: Aeneas emitted sorry"; exit 1; fi
echo "generated Lean identical for host and wasm32 translations"

step "4. forbidden constructs in hand-written Lean"
for f in lean/Boundary.lean lean/Proofs.lean lean/Axioms.lean lean/pure/*.lean; do
  if grep -nE '\b(sorry|admit|axiom|native_decide|implemented_by|extern)\b' "$f"; then
    echo "FAIL: forbidden construct in $f"; exit 1; fi
  # bv_decide (native-code axioms): rejected outside comments, as in pure-lean/check.sh
  if grep -nE '^[^-]*\bbv_decide\b' "$f"; then echo "FAIL: bv_decide in $f"; exit 1; fi
done
if grep -nE '\b(RefDecoder|Utf8Pure|LoopInv|StRel|PendRel)\b' lean/Boundary.lean; then
  echo "FAIL: Boundary.lean mentions proof internals"; exit 1; fi
echo "none (no sorry/admit/axiom/native_decide/implemented_by/extern/bv_decide)"

step "5. build Lean"
if [ "$FAST" = --fast ] && [ -f lean/build/Utf8Proofs.olean ]; then
  echo "(--fast: reusing pure-layer build)"
else
  lean/build_pure.sh
fi
(cd lean && ./build.sh Decoder/Types.lean Decoder/Funs.lean Boundary.lean Proofs.lean) 2>&1 \
  | grep -E '^==|error|sorry' || true
(cd lean && ./build.sh Proofs.lean > "$T/proofs.log" 2>&1) || { cat "$T/proofs.log"; exit 1; }
if grep -q "declaration uses .sorry" "$T/proofs.log"; then echo "FAIL: sorry"; exit 1; fi

step "6. axioms"
(cd lean && ./build.sh Axioms.lean) 2>&1 | tee "$T/axioms.txt"
BAD=$(grep -o '\[[^]]*\]' "$T/axioms.txt" | tr -d '[] ' | tr ',' '\n' \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)
[ -z "$BAD" ] || { echo "FAIL: unexpected axioms: $BAD"; exit 1; }
[ "$(grep -c 'depends on axioms' "$T/axioms.txt")" = 3 ] || { echo "FAIL: axioms output"; exit 1; }

step "7. difftest harness"
if [ "$FAST" = --fast ]; then node "$CAND/difftest/run.mjs" "$HERE/decoder.mjs" --no-huge | tail -5
else node "$CAND/difftest/run.mjs" "$HERE/decoder.mjs" | tail -5; fi

step "ALL CHECKS PASSED"
