#!/bin/sh
# Build everything, check the spec copy, reject proof holes, print assumptions.
set -e
cd "$(dirname "$0")"
eval $(opam env --switch=wasmcert) 2>/dev/null
make
echo "== checking for holes"
if grep -nE '\b(Admitted|admit|Axiom|Parameter|Abort)\b' Utf8Ref.v Utf8Check.v Utf8Proofs.v; then
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
coqc -Q . Utf8 PrintAssumptions.v 2>&1 | grep -v 'Running as root'
