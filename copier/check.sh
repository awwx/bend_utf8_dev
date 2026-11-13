#!/usr/bin/env bash
# Compile sources afresh with the pinned Lean toolchain; never reuse repo oleans.
set -euo pipefail
cd "$(dirname "$0")"
TC=leanprover/lean4:v4.35.0
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
PURE=../candidates/pure-lean
SPEC=../candidates/spec-lean/Utf8Laws.lean
FILES=(Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs Utf8StepFacts Utf8Roundtrip StreamModel)
command cp "$SPEC" "$OUT/Utf8Laws.lean"
for f in Utf8Bits Utf8Ref Utf8Table Utf8Proofs Utf8StepFacts; do
  command cp "$PURE/$f.lean" "$OUT/$f.lean"
done
for f in Utf8Roundtrip StreamModel; do command cp "$f.lean" "$OUT/$f.lean"; done
cmp "$SPEC" "$OUT/Utf8Laws.lean"
for f in "${FILES[@]}"; do
  if grep -nE '\b(sorry|axiom|native_decide|unsafe|implemented_by|extern|admit)\b' "$OUT/$f.lean"; then
    echo "FAIL: forbidden construct in $f.lean"; exit 1
  fi
  if grep -nE '^[^-]*\bbv_decide\b' "$OUT/$f.lean"; then
    echo "FAIL: bv_decide tactic in $f.lean"; exit 1
  fi
done
echo "== $TC (fresh temporary build)"
cd "$OUT"
for f in "${FILES[@]}"; do
  LEAN_PATH="$OUT" elan run "$TC" lean -o "$OUT/$f.olean" "$f.lean"
done
cat > "$OUT/Audit.lean" <<'LEAN'
import StreamModel
#print axioms Copier.valid_roundtrip
#print axioms Copier.textEvents_scalar
#print axioms Copier.good_copy
#print axioms Copier.executions_exist
#print axioms Copier.bad_counterexample
LEAN
LEAN_PATH="$OUT" elan run "$TC" lean Audit.lean > "$OUT/axioms.txt"
cat "$OUT/axioms.txt"
N=$(grep -cE "depends on axioms|does not depend" "$OUT/axioms.txt")
[ "$N" = 5 ] || { echo "FAIL: expected 5 axiom audit results, got $N"; exit 1; }
BAD=$(tr -d '\n' < "$OUT/axioms.txt" | grep -oE '\[[^]]*\]' | tr -d '[] ' | tr ',' '\n' | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)
if [ -n "$BAD" ]; then echo "FAIL: unexpected axioms: $BAD"; exit 1; fi
echo "ALL COPIER CHECKS PASSED"
