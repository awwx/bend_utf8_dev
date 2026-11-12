#!/usr/bin/env bash
# Build everything, check the spec copy, reject proof holes, print assumptions.
# Three guards against an assumption (axiom, Admitted, checker switch) in the
# pure layer:
#  1. Print Assumptions must say "Closed under the global context" for the 15
#     laws, RefDecoder_correct, and EVERY top-level Theorem/Lemma/Definition/
#     Fixpoint/... declared in Utf8Ref.v, Utf8Bridge.v, Utf8Proofs.v and
#     Utf8StepFacts.v (the list is generated from the sources, so it covers
#     every result the Wasm decoder proofs can use);
#  2. rocqchk -o (kernel re-check of the five Utf8 modules) prints the axioms
#     of the whole loaded context, used or not: it must list no axiom other
#     than the two Stdlib/Corelib module-type parameter families it always
#     shows (PeanoNat.Nat.PrivateImplementsBitwiseSpec.*, ssrunder.Under_rel.*),
#     and no type-in-type, unsafe fixpoint or assumed positivity;
#  3. holes.pl (second line of defence): forbidden words and commands
#     (Admitted, admit, Axiom(s), Parameter(s), Conjecture(s), Abort, Primitive,
#     bypass_check, Unset other than two printing/implicit options, ...) and
#     Hypothesis/Variable/Context outside a Section.
set -euo pipefail
cd "$(dirname "$0")"
eval $(opam env --switch=wasmcert) 2>/dev/null
FILES="Utf8Ref.v Utf8Bridge.v Utf8Proofs.v Utf8StepFacts.v"
make
echo "== checking for holes (holes.pl)"
perl holes.pl $FILES || { echo "FAIL: proof holes found"; exit 1; }
echo "none in $FILES"
echo "== Print Assumptions"
cat > PrintAssumptions.v <<'EOV'
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs Utf8StepFacts.
EOV
NLAWS=0
for t in bit8_value_sum bit8_value_word u32_byte4_bits is_surrogate_code_point_examples \
         begins_with_scalar_unique not_valid_sequence_prefix_extended maximal_subpart_exists \
         maximal_subpart_unique decodes_first_exists decodes_first_unique decodes_first_empty \
         decodes_first_nonempty decodes_exists decodes_unique decodes_examples; do
  echo "Check ${t}_proved : ${t}. Print Assumptions ${t}_proved." >> PrintAssumptions.v
  NLAWS=$((NLAWS+1))
done
echo "Check RefDecoder_correct : Decoder_correct RefDecoder. Print Assumptions RefDecoder_correct." >> PrintAssumptions.v
# Every top-level declaration of the four build files, fully qualified.
NDECL=0
for f in $FILES; do
  m=${f%.v}
  for n in $(sed -n -E "s/^(Theorem|Lemma|Corollary|Fact|Remark|Proposition|Definition|Fixpoint|CoFixpoint|Example|Let|Inductive|Variant|Record|Instance)[[:space:]]+([A-Za-z_][A-Za-z0-9_']*).*/\2/p" "$f"); do
    echo "Print Assumptions Utf8.$m.$n." >> PrintAssumptions.v
    NDECL=$((NDECL+1))
  done
done
NEXP=$((NLAWS + 1 + NDECL))
# Every Check must succeed (a failing Check or build error is fatal) and every
# Print Assumptions must say "Closed under the global context" (no axioms at all).
# Each Print Assumptions takes about 0.25 s, so the file is split into 4 parts
# compiled in parallel (PrintAssumptions.v keeps the whole list for reference).
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
head -1 PrintAssumptions.v > "$W/hdr"
tail -n +2 PrintAssumptions.v > "$W/body"
split -n l/4 -d "$W/body" "$W/part"
pids=()
for p in "$W"/part0[0-3]; do
  b=PA_$(basename "$p")
  cat "$W/hdr" "$p" > "$W/$b.v"
  ( coqc -Q . Utf8 "$W/$b.v" > "$W/$b.out" 2>&1 || echo FAILED >> "$W/$b.out" ) &
  pids+=($!)
done
wait "${pids[@]}"
OUT="$W/all.out"; cat "$W"/PA_part0[0-3].out > "$OUT"
if grep -q '^FAILED$' "$OUT"; then cat "$OUT"; echo "FAIL: PrintAssumptions.v"; exit 1; fi
CHK="$W/chk.log"
N=$(grep -c 'Closed under the global context' "$OUT" || true)
P=$(grep -o 'Print Assumptions' PrintAssumptions.v | wc -l)
if [ "$N" != "$NEXP" ] || [ "$P" != "$NEXP" ]; then
  grep -v 'Running as root' "$OUT" | grep -v 'Closed under the global context' | head -40
  echo "FAIL: expected $NEXP 'Closed under the global context' (of $P Print Assumptions), got $N"; exit 1
fi
grep -v 'Running as root' "$OUT" | grep -v 'Closed under the global context' || true
echo "$N x Closed under the global context ($NLAWS laws, RefDecoder_correct, $NDECL declarations of $FILES)"
echo "== rocqchk -o: kernel re-check of the Utf8 modules and the axioms of the whole context"
MODS=""; for f in Utf8Laws.v $FILES; do MODS="$MODS -norec Utf8.${f%.v}"; done
rocqchk -o -Q . Utf8 $MODS > "$CHK" 2>&1 || { tail -30 "$CHK"; echo "FAIL: rocqchk"; exit 1; }
grep -q 'Modules were successfully checked' "$CHK" || { tail -30 "$CHK"; echo "FAIL: rocqchk did not report success"; exit 1; }
AX=$(sed -n '/^\* Axioms:/,/^\* /p' "$CHK" | sed '1d;$d' | sed 's/^ *//;/^$/d')
[ -n "$AX" ] || { sed -n '/^CONTEXT SUMMARY/,$p' "$CHK"; echo "FAIL: rocqchk context summary not found"; exit 1; }
if printf '%s\n' "$AX" | grep -vE '^(Stdlib\.Arith\.PeanoNat\.Nat\.PrivateImplementsBitwiseSpec|Corelib\.ssr\.ssrunder\.Under_rel)\.[A-Za-z0-9_]+$'; then
  echo "FAIL: rocqchk lists the axioms above in the context"; exit 1; fi
for k in 'type-in-type' 'unsafe (co)fixpoints' 'positivity is assumed'; do
  grep -F "$k" "$CHK" | grep -q ': <none>$' || { sed -n '/^CONTEXT SUMMARY/,$p' "$CHK"; echo "FAIL: rocqchk: '$k' is not <none>"; exit 1; }
done
grep -q 'Set is predicative' "$CHK" || { echo "FAIL: rocqchk: impredicative Set"; exit 1; }
echo "context axioms: only the $(printf '%s\n' "$AX" | wc -l) Stdlib/Corelib module-type parameters; no type-in-type, unsafe fixpoint or assumed positivity"
echo "ALL CHECKS PASSED ($NLAWS laws, RefDecoder_correct, all $NDECL declarations of the build files: no axioms; rocqchk context clean)"
