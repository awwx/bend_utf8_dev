#!/usr/bin/env bash
# Build the pure layer under both toolchains, check for forbidden
# constructs, and print axioms of the exported theorems.
set -euo pipefail
cd "$(dirname "$0")"
SPEC=../spec-lean/Utf8Laws.lean
FILES="Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs"

# 1. The spec is used unmodified.
command cp "$SPEC" Utf8Laws.lean
cmp "$SPEC" Utf8Laws.lean || { echo "FAIL: spec copy differs"; exit 1; }
echo "spec: Utf8Laws.lean byte-identical to $SPEC"

# 2. Forbidden constructs in compiled files (comments included, to be strict).
for f in $FILES Utf8Eval; do
  if grep -nE '\b(sorry|axiom|native_decide|unsafe|implemented_by|extern|admit)\b' "$f.lean"; then
    echo "FAIL: forbidden construct in $f.lean"; exit 1
  fi
  # bv_decide is allowed by the brief but trusts native code; this layer avoids it.
  if grep -nE '^[^-]*\bbv_decide\b' "$f.lean"; then
    echo "FAIL: bv_decide tactic use in $f.lean"; exit 1
  fi
done
echo "no sorry/axiom/native_decide/unsafe/implemented_by/extern/admit/bv_decide"

THMS="bit8_value_sum_proved bit8_value_word_proved u32_byte4_bits_proved
is_surrogate_code_point_examples_proved begins_with_scalar_unique_proved
not_valid_sequence_prefix_extended_proved maximal_subpart_exists_proved
maximal_subpart_unique_proved decodes_first_exists_proved decodes_first_unique_proved
decodes_first_empty_proved decodes_first_nonempty_proved decodes_exists_proved
decodes_unique_proved decodes_examples_proved RefDecoder_correct"

# 3. Build under both toolchains, each into its own output directory.
for TC in leanprover/lean4:v4.35.0 leanprover/lean4:v4.36.0-rc2; do
  OUT=$(mktemp -d)
  echo "== $TC"
  for f in $FILES; do
    LEAN_PATH=$OUT elan run "$TC" lean -o "$OUT/$f.olean" "$f.lean"
  done
  R=$(LEAN_PATH=$OUT elan run "$TC" lean Utf8Eval.lean)
  [ "$R" = "true" ] || { echo "FAIL: Utf8Eval.lean printed: $R"; exit 1; }
  echo "evaluation sanity test: true"
  AX="$OUT/Axioms.lean"
  { echo "import Utf8Proofs"; echo "open Utf8Pure";
    for t in $THMS; do echo "#print axioms $t"; done
    # Each theorem has exactly the type of the spec's law (a failure is a build error).
    for t in $THMS; do case $t in
      RefDecoder_correct) echo "example : Decoder.Correct RefDecoder := RefDecoder_correct" ;;
      *) echo "example : ${t%_proved} := $t" ;; esac; done; } > "$AX"
  LEAN_PATH=$OUT elan run "$TC" lean "$AX" > "$OUT/axioms.txt" 2>&1 \
    || { cat "$OUT/axioms.txt"; echo "FAIL: theorem types / axioms check"; exit 1; }
  cat "$OUT/axioms.txt"
  if grep -q sorryAx "$OUT/axioms.txt"; then echo "FAIL: sorryAx"; exit 1; fi
  BAD=$(tr -d '\n' < "$OUT/axioms.txt" | grep -o '\[[^]]*\]' | tr -d '[] ' | tr ',' '\n' \
        | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)
  if [ -n "$BAD" ]; then echo "FAIL: unexpected axioms: $BAD"; exit 1; fi
  N=$(grep -cE "depends on axioms|does not depend" "$OUT/axioms.txt")
  [ "$N" = 16 ] || { echo "FAIL: expected 16 #print axioms results, got $N"; exit 1; }
  rm -rf "$OUT"
  echo "== $TC OK"
done
echo "ALL CHECKS PASSED"
