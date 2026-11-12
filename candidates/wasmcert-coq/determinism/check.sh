#!/bin/bash
# Build the determinism development from clean state, print assumptions,
# and give a verdict.  Needs: eval $(opam env --switch=wasmcert).
# Depends only on the installed coq-wasm (WasmCert-Coq 2.2.1); nothing
# outside this directory is read.  The decoder's instance of the result
# (decoder_call_outcome) lives in ../decoder/DetInstance.v.
set -u
cd "$(dirname "$0")"
eval $(opam env --switch=wasmcert 2>/dev/null)
make clean >/dev/null 2>&1
start=$(date +%s)
if ! make 2>&1; then echo "VERDICT: FAIL (build error)"; exit 1; fi
echo "build: $(( $(date +%s) - start )) s"
# Holes in the build (the wip/ directory is outside the build).
holes=$(grep -nwE 'Admitted|admit|Axiom|Parameter|Abort' $(grep '\.v$' _CoqProject))
if [ -n "$holes" ]; then echo "holes found:"; echo "$holes"; echo "VERDICT: FAIL (holes)"; exit 1; fi
echo "no Admitted/admit/Axiom/Parameter in the build files"
rocq c -w -notation-overridden,-notation-for-abbreviation -Q . Determinism Assumptions.v 2>&1 | tee assumptions.out
if grep -q "Determinism\.\|Fragment\." assumptions.out; then
  echo "VERDICT: FAIL (an assumption comes from this development)"; exit 1; fi
# Which of the three statements of ReduceDet.v have a proof in the build:
# each must exist under its _proved name with exactly the statement's type.
missing=""
for st in reduce_det_fragment fragment_step_preserved trapped_step_preserved; do
  printf 'From Determinism Require Import Fragment ReduceDet Trapped Preservation Focus HeadStep Det Main.\nCheck (%s_proved : %s).\n' "$st" "$st" > Probe.v
  if rocq c -Q . Determinism Probe.v >/dev/null 2>&1; then
    echo "proved in the build: $st"
  else
    missing="$missing $st"
  fi
done
rm -f Probe.v Probe.vo Probe.glob .Probe.aux Probe.vok Probe.vos
if [ -n "$missing" ]; then
  echo "VERDICT: PARTIAL -- builds, no holes, no new axioms; NOT yet proved:$missing"
  exit 0
fi
# The unconditional end results must exist with the intended statements.
cat > Probe.v <<'PROBE'
From mathcomp Require Import ssreflect ssrbool seq.
From Wasm Require Import datatypes operations opsem.
From Determinism Require Import Fragment ReduceDet Trapped Preservation Det Main.
Section P. Context `{ho: host}.
Check (fragment_deterministic_outcome : forall hs s f es hs' s' f' vs,
  cfg_ok s es ->
  reduce_trans (hs, s, f, es) (hs', s', f', v_to_e_list vs) ->
  deterministic_outcome (hs, s, f, es) (hs', s', f', v_to_e_list vs)).
Check (still_reaches_stuck_is_target : forall c D : host_state * store_record * frame * seq administrative_instruction,
  (forall c', reduce_trans c c' -> reduce_trans c' D) ->
  forall c', reduce_trans c c' -> (forall c'', ~ reduce_tuple c' c'') -> c' = D).
End P.
PROBE
if rocq c -w -notation-overridden,-notation-for-abbreviation -Q . Determinism Probe.v >probe.out 2>&1; then
  echo "unconditional end results present: fragment_deterministic_outcome, still_reaches_stuck_is_target"
  echo "VERDICT: ALL PROVED -- reduce_det_fragment, the deterministic-outcome corollary and still_reaches_stuck_is_target, no holes, no new axioms; depends only on coq-wasm"
else
  cat probe.out
  echo "VERDICT: FAIL (end-result probe)"; rm -f Probe.v Probe.vo Probe.glob .Probe.aux Probe.vok Probe.vos probe.out; exit 1
fi
rm -f Probe.v Probe.vo Probe.glob .Probe.aux Probe.vok Probe.vos probe.out
