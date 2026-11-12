#!/usr/bin/env bash
# Build everything, check the spec copy, reject proof holes, print assumptions.
set -euo pipefail
cd "$(dirname "$0")"
eval $(opam env --switch=wasmcert) 2>/dev/null
make
echo "== checking for holes"
if grep -nE '\b(Admitted|admit|Axiom|Parameter|Abort)\b' Utf8Ref.v Utf8Bridge.v Utf8Proofs.v; then
  echo "FAIL: proof holes found"; exit 1
fi
echo "no Admitted/admit/Axiom/Parameter/Abort in the build files"
echo "== Print Assumptions"
cat > PrintAssumptions.v <<'EOV'
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs.
EOV
for t in bit8_value_sum bit8_value_word u32_byte4_bits is_surrogate_code_point_examples \
         begins_with_scalar_unique not_valid_sequence_prefix_extended maximal_subpart_exists \
         maximal_subpart_unique decodes_first_exists decodes_first_unique decodes_first_empty \
         decodes_first_nonempty decodes_exists decodes_unique decodes_examples; do
  echo "Check ${t}_proved : ${t}. Print Assumptions ${t}_proved." >> PrintAssumptions.v
done
echo "Check RefDecoder_correct : Decoder_correct RefDecoder. Print Assumptions RefDecoder_correct." >> PrintAssumptions.v
echo "Print Assumptions step_output_ok." >> PrintAssumptions.v
# Every Check must succeed (a failing Check or build error is fatal) and every
# Print Assumptions must say "Closed under the global context" (no axioms at all).
OUT=$(mktemp); trap 'rm -f "$OUT"' EXIT
coqc -Q . Utf8 PrintAssumptions.v > "$OUT" 2>&1 || { cat "$OUT"; echo "FAIL: PrintAssumptions.v"; exit 1; }
grep -v 'Running as root' "$OUT" || true
N=$(grep -c 'Closed under the global context' "$OUT" || true)
[ "$N" = 17 ] || { echo "FAIL: expected 17 'Closed under the global context', got $N"; exit 1; }
echo "ALL CHECKS PASSED (15 laws, RefDecoder_correct, step_output_ok: no axioms)"
