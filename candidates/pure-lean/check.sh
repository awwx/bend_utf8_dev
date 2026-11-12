#!/usr/bin/env bash
# Build the pure layer under both toolchains, check for forbidden
# constructs, and print axioms of the exported theorems; then, on each
# toolchain, replay every constant of the pure layer in the kernel (step 4).
# Usage: ./check.sh [--skip-replay]   (the final line then says replay SKIPPED)
# CHECK_REPLAY_TIMEOUT (seconds, default 300) bounds each replay.
set -euo pipefail
cd "$(dirname "$0")"
SKIP_REPLAY=no
for a in "$@"; do
  case $a in
    --skip-replay) SKIP_REPLAY=yes ;;
    *) echo "usage: $0 [--skip-replay]"; exit 2 ;;
  esac
done
REPLAY_TIMEOUT=${CHECK_REPLAY_TIMEOUT:-300}
REPLAY_NOTES=
SPEC=../spec-lean/Utf8Laws.lean
FILES="Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs Utf8StepFacts"

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
  { echo "import Utf8StepFacts"; echo "open Utf8Pure";
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
  # 4. Kernel replay: re-check, in a fresh environment importing only Init/Lean/Std,
  # every other constant of Utf8StepFacts' import closure (all six files above), so a
  # declaration added by metaprogramming without kernel checking is rejected.  Then,
  # on the replayed environment: each of the 16 theorems has exactly the law's type,
  # and its axioms, recomputed from the replayed constants (#print axioms above
  # uses per-module lists stored in the .olean files), are within the standard three.
  if [ "$SKIP_REPLAY" = yes ]; then
    echo "kernel replay SKIPPED (--skip-replay)"; REPLAY_NOTES="$REPLAY_NOTES $TC: SKIPPED;"
  else
    { cat <<'EOF'
import Lean
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let full ← importModules #[{module := `Utf8StepFacts}] {} (loadExts := false)
  let base ← importModules #[{module := `Init}, {module := `Lean}, {module := `Std}] {} (loadExts := false)
  let mut news : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in full.constants.map₁.toList do
    if !base.contains n then news := news.insert n ci
  IO.println s!"replaying {news.size} constants (all of Utf8StepFacts' imports except Init/Lean/Std)"
  let kenv ← base.toKernelEnv.replay news
  let axiomsOf (c : Name) : Except String (Array Name) := Id.run do
    let mut seen : NameSet := {}
    let mut todo := #[c]
    let mut axs : NameSet := {}
    while h : todo.size > 0 do
      let d := todo.back; todo := todo.pop
      if seen.contains d then continue
      seen := seen.insert d
      let some ci := kenv.find? d | return .error s!"{d} (used by {c}) missing from the replayed environment"
      if ci matches .axiomInfo _ then axs := axs.insert d
      let mut es := #[ci.type]
      if let some v := ci.value? (allowOpaque := true) then es := es.push v
      for e in es do
        for u in e.getUsedConstants do todo := todo.push u
      if let .inductInfo v := ci then todo := todo ++ v.ctors.toArray
    return .ok (axs.toArray.qsort Name.lt)
  let check (thm : Name) (ty : Expr) : IO Unit := do
    unless news.contains thm do throw <| IO.userError s!"{thm} not among the replayed constants"
    match kenv.find? thm with
    | some (.thmInfo t) =>
      unless t.type == ty do throw <| IO.userError s!"replayed {thm} does not have type {ty}"
    | _ => throw <| IO.userError s!"{thm} is not a theorem in the replayed environment"
    match axiomsOf thm with
    | .error e => throw <| IO.userError e
    | .ok axs =>
      unless axs.all ([`propext, `Classical.choice, `Quot.sound].contains ·) do
        throw <| IO.userError s!"replayed {thm} depends on axioms {axs.toList}"
  check `Utf8Pure.RefDecoder_correct (.app (.const `Decoder.Correct []) (.const `Utf8Pure.RefDecoder []))
  for law in LAWS do
    check (Name.mkStr `Utf8Pure (law ++ "_proved")) (.const (Name.mkStr .anonymous law) [])
  IO.println "replay OK"
EOF
    } | sed "s/LAWS/[$(for t in $THMS; do [ "$t" = RefDecoder_correct ] || printf '"%s", ' "${t%_proved}"; done | sed 's/, $//')]/" > "$OUT/Replay.lean"
    rc=0; LEAN_PATH=$OUT timeout --kill-after=20 "$REPLAY_TIMEOUT" elan run "$TC" lean --run "$OUT/Replay.lean" \
      > "$OUT/replay.txt" 2>&1 || rc=$?
    cat "$OUT/replay.txt"
    if [ "$rc" = 124 ] || [ "$rc" = 137 ]; then echo "FAIL: TIMEOUT: kernel replay ($TC) exceeded $REPLAY_TIMEOUT s"; exit 1; fi
    [ "$rc" = 0 ] && [ "$(tail -1 "$OUT/replay.txt")" = "replay OK" ] \
      || { echo "FAIL: kernel replay rejected the environment ($TC)"; exit 1; }
    n=$(sed -n 's/^replaying \([0-9]*\) .*/\1/p' "$OUT/replay.txt")
    REPLAY_NOTES="$REPLAY_NOTES $TC: $n constants OK;"
  fi
  rm -rf "$OUT"
  echo "== $TC OK"
done
if [ "$SKIP_REPLAY" = yes ]; then echo "ALL CHECKS PASSED (kernel replay SKIPPED (--skip-replay) on both toolchains)"
else echo "ALL CHECKS PASSED (kernel replay of all non-core constants, 16 theorem types and recomputed axioms:${REPLAY_NOTES%;})"; fi
