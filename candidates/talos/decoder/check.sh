#!/usr/bin/env bash
# Check of the Talos decoder candidate: the top-level claim
# Utf8Boundary.ShippedModuleCorrect (Boundary.lean) is proved as
# Utf8Wasm.shippedModuleCorrect (ProofMain.lean), and the non-vacuity claim
# Utf8Boundary.ShippedWrapperCovered (the wrapper's calls meet every condition of
# the guarantees) is proved as Utf8Wasm.shippedWrapperCovered (ProofWrapper.lean);
# see STATUS.txt.  The final "PASS:" line is printed only after every step below
# succeeded, including `example : Utf8Boundary.ShippedModuleCorrect :=
# Utf8Wasm.shippedModuleCorrect` and the same for ShippedWrapperCovered (so the
# theorems have exactly the pinned Boundary types) and an exact comparison of
# their axiom lists with [propext, Classical.choice, Quot.sound].  Any failing
# step exits non-zero.
#
# Steps: pinned hashes of the reviewed files; the shipped decoder.wasm equals a
# rebuild from decoder.wat and its `wasm-tools print` text equals
# decoder.printed.wat (the text Boundary.lean / DecoderModule.lean include);
# the wrapper's layout constants (decoder.mjs) and the module's memory size
# (decoder.printed.wat) equal the constants in Boundary.lean; spec / pure-layer
# copies; forbidden constructs; clean Lean build; statements
# and axioms of the intermediate results; the top-level theorem's type and
# axioms; difftest on the shipped bytes.
#
# Depends on (not built here): the Talos checkout built in ../talos (see
# ../SETUP.md) and wasm-tools in ../tools.  The checkout must be at TALOS_COMMIT
# below with a clean worktree (build output ignored) and up-to-date .olean files.
#
# Usage: ./check.sh [--skip-replay] [--refresh-copies]
#   --skip-replay     skip the kernel replay (about 2 min, 7 GB RAM); the PASS line
#                     then says "kernel replay SKIPPED".
#   --refresh-copies  copy pure-lean/Utf8*.lean over stale build copies in this
#                     directory (without it a stale copy is a FAIL).
# Timeouts (seconds, environment): CHECK_STEP_TIMEOUT (default 600) for each Lean
# file, statement check and the difftest; CHECK_REPLAY_TIMEOUT (default 1500) for the
# replay.  A step that runs longer is killed and the check FAILs naming the step
# (a safety net: the proof files keep Lean's default heartbeat limit, so a broken
# proof should fail on its own).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
SKIP_REPLAY=no; REFRESH=no
for a in "$@"; do
  case $a in
    --skip-replay) SKIP_REPLAY=yes ;;
    --refresh-copies) REFRESH=yes ;;
    *) echo "usage: $0 [--skip-replay] [--refresh-copies]"; exit 2 ;;
  esac
done
STEP_TIMEOUT=${CHECK_STEP_TIMEOUT:-600}
REPLAY_TIMEOUT=${CHECK_REPLAY_TIMEOUT:-1500}
CAND=$(cd "$here/../.." && pwd)
WT=$CAND/talos/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools
TALOS_REPO=$CAND/talos/talos
TALOS=$TALOS_REPO/interpreter
# Pinned Talos commit (../SETUP.md).  Talos defines the semantics the theorem is
# about; change only after reviewing the new Talos version.
TALOS_COMMIT=d7c84ac660757953b752bdfc9cb8dae3dab623ed
PURE=$CAND/pure-lean
SPEC=$CAND/spec-lean/Utf8Laws.lean
TC=$(cat lean-toolchain)
LEANC="elan run $TC lean"
T=$(mktemp -d)
DT_PID=
# On exit, stop a still-running background difftest (its `timeout` forwards the
# signal to node), then remove the temp dir.
trap 'if [ -n "$DT_PID" ]; then pkill -TERM -P "$DT_PID" 2>/dev/null; kill "$DT_PID" 2>/dev/null; fi; rm -rf "$T"' EXIT
fail() { echo "FAIL: $*"; exit 1; }
# limited SECS LABEL LOG CMD...: run CMD with output to LOG; FAIL if it is still
# running after SECS seconds (timeout signals the whole process group, so the
# lean process under `elan run` is killed too).  Returns CMD's exit status.
limited() {
  local secs=$1 label=$2 log=$3 rc=0; shift 3
  timeout --kill-after=20 "$secs" "$@" > "$log" 2>&1 || rc=$?
  if [ "$rc" = 124 ] || [ "$rc" = 137 ]; then
    tail -20 "$log"; fail "TIMEOUT: $label did not finish within ${secs} s (killed)"; fi
  return "$rc"
}

SPEC_SHA=29396a7e1f013ee5a8cee9b3fb94a186e0f809bd68717f7b3046508cfe3b0583      # spec-lean/Utf8Laws.lean
BOUNDARY_SHA=9058323caddcf8aed8d8d6e4dee7f46009149121fae719be0b735061a8988ab1  # Boundary.lean

echo "== dependencies"
[ -x "$WT" ] || fail "wasm-tools not found at $WT (see ../SETUP.md)"
[ -d "$TALOS/.lake/build" ] || fail "Talos interpreter not built in $TALOS (see ../SETUP.md)"
[ "$(cat "$TALOS/lean-toolchain")" = "$TC" ] || fail "Talos toolchain $(cat "$TALOS/lean-toolchain") != $TC"
echo "wasm-tools $($WT --version); Talos at $TALOS; Lean $TC"

echo "== Talos checkout: pinned commit, clean worktree, .olean files up to date"
head=$(git -C "$TALOS_REPO" rev-parse HEAD) || fail "$TALOS_REPO is not a git checkout"
[ "$head" = "$TALOS_COMMIT" ] || fail "Talos checkout is at $head, not the pinned $TALOS_COMMIT"
# --porcelain lists modified, staged and untracked files; ignored build output
# (.lake/) is not listed.
dirty=$(git -C "$TALOS_REPO" status --porcelain --untracked-files=all)
[ -z "$dirty" ] || { echo "$dirty"; fail "Talos checkout has local modifications (listed above)"; }
TALOS_MODS=$(cat *.lean | sed -n 's/^import \(Interpreter\.[A-Za-z0-9_.]*\).*/\1/p' | sort -u)
(cd "$TALOS" && lake build --no-build $TALOS_MODS) > "$T/lake.log" 2>&1 \
  || { cat "$T/lake.log"; fail "Talos .olean files are not up to date with the checkout (rebuild per ../SETUP.md)"; }
echo "Talos at $TALOS_COMMIT, clean; up to date: $(echo $TALOS_MODS)"

echo "== reviewed files match their pinned hashes"
echo "$SPEC_SHA  $SPEC" | sha256sum -c - || fail "spec-lean/Utf8Laws.lean is not the audited spec"
echo "$BOUNDARY_SHA  Boundary.lean" | sha256sum -c - || fail "Boundary.lean differs from the reviewed version"

echo "== wasm: shipped bytes = rebuild from decoder.wat; printed text = decoder.printed.wat"
$WT parse decoder.wat -o "$T/unstripped.wasm"
$WT strip --all -o "$T/rebuilt.wasm" "$T/unstripped.wasm"
cmp "$T/rebuilt.wasm" decoder.wasm || fail "shipped decoder.wasm differs from a rebuild of decoder.wat"
$WT validate decoder.wasm
$WT print decoder.wasm > "$T/printed.wat"
cmp decoder.printed.wat "$T/printed.wat" || { diff decoder.printed.wat "$T/printed.wat" || true; fail "decoder.printed.wat is not the printed text of the shipped decoder.wasm"; }
sha256sum decoder.wasm decoder.printed.wat

echo "== wrapper layout constants and memory size = the constants in Boundary.lean"
# decoder.mjs declares each constant on one line marked "// LAYOUT <name>";
# Boundary.lean defines `def <name> : Nat := <decimal>`.  Both sides must give
# exactly one plain decimal value per name.  (The memory size is also proved
# from the decoded module in ProofWrapper.lean; this compares it textually too.)
lean_const() {
  local v; v=$(sed -n "s/^def $1 : Nat := \([0-9][0-9]*\)\$/\1/p" Boundary.lean)
  [ "$(printf '%s\n' "$v" | grep -c .)" = 1 ] || { echo "FAIL: Boundary.lean: no single 'def $1 : Nat := <decimal>' line" >&2; return 1; }
  echo "$v"; }
js_const() {
  local v; v=$(sed -n "s|^const [A-Z][A-Z]* = \([0-9][0-9]*\); *// LAYOUT $1\( .*\)\{0,1\}\$|\1|p" decoder.mjs)
  [ "$(printf '%s\n' "$v" | grep -c .)" = 1 ] || { echo "FAIL: decoder.mjs: no single 'const X = <decimal>; // LAYOUT $1' line" >&2; return 1; }
  echo "$v"; }
[ "$(grep -c '// LAYOUT ' decoder.mjs)" = 3 ] || fail "decoder.mjs must have exactly three '// LAYOUT' lines"
for c in wrapperInputAddr wrapperMaxChunk wrapperOutputAddr; do
  l=$(lean_const $c) || exit 1; j=$(js_const $c) || exit 1
  [ "$l" = "$j" ] || fail "layout constant $c: decoder.mjs has $j, Boundary.lean has $l"
  echo "$c = $l"
done
wp=$(sed -n 's/^  (memory (;0;) \([0-9][0-9]*\))$/\1/p' decoder.printed.wat)
[ "$(printf '%s\n' "$wp" | grep -c .)" = 1 ] || fail "decoder.printed.wat: no single '(memory (;0;) <pages>)' line"
grep -q 'memory\.grow' decoder.printed.wat && fail "module contains memory.grow"
lp=$(lean_const shippedMemoryPages) || exit 1
[ "$wp" = "$lp" ] || fail "memory size: module has $wp pages, Boundary.lean shippedMemoryPages = $lp"
echo "shippedMemoryPages = $lp (module text); no memory.grow in the module"

# The difftest only needs the shipped decoder.wasm checked above; it runs in the
# background during the Lean steps and is waited for (and its result checked) at
# the end.
limited "$STEP_TIMEOUT" "difftest" "$T/dt.log" node "$CAND/difftest/run.mjs" "$here/decoder.mjs" &
DT_PID=$!

echo "== spec and pure layer copies"
cmp "$SPEC" "$PURE/Utf8Laws.lean" || fail "pure-lean/Utf8Laws.lean differs from the spec"
for f in Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs Utf8StepFacts; do
  if ! cmp -s "$PURE/$f.lean" "$f.lean"; then
    if [ "$REFRESH" = yes ]; then
      echo "note: $f.lean was stale; refreshing it from pure-lean/ (--refresh-copies)"
      command cp "$PURE/$f.lean" "$f.lean"
    else
      diff "$PURE/$f.lean" "$f.lean" | head -20 || true
      fail "build copy $f.lean differs from pure-lean/$f.lean (rerun with --refresh-copies to copy pure-lean/ over it)"
    fi
  fi
  cmp "$PURE/$f.lean" "$f.lean" || fail "build copy $f.lean differs from pure-lean/$f.lean"
done
cmp "$SPEC" Utf8Laws.lean || fail "build copy Utf8Laws.lean is not the spec"
echo "copies identical to pure-lean/; Utf8Laws.lean identical to the pinned spec"

OURS="DecoderModule Boundary ProofMach ProofFuncs ProofStep ProofLayout ProofLoop ProofBuffer ProofDone ProofModel ProofRefine ProofMain ProofWrapper Axioms"
echo "== forbidden constructs"
FORBID='\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|skipKernelTC)\b|#exit|set_option +debug\.'
for f in $OURS Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs Utf8StepFacts; do
  if grep -nE "$FORBID" "$f.lean"; then fail "forbidden construct in $f.lean"; fi
  # bv_decide (native-code axioms): rejected outside comments, as in pure-lean/check.sh
  if grep -nE '^[^-]*\bbv_decide\b' "$f.lean"; then fail "bv_decide in $f.lean"; fi
done
echo "none"

echo "== lean (clean build; every error is fatal)"
export LEAN_PATH=$(cd "$TALOS" && lake env printenv LEAN_PATH):$here/build
rm -rf build; mkdir -p build
for f in Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs Utf8StepFacts DecoderModule Boundary ProofMach ProofFuncs \
         ProofStep ProofLayout ProofLoop ProofBuffer ProofDone ProofModel ProofRefine \
         ProofMain ProofWrapper; do
  s=$(date +%s)
  limited "$STEP_TIMEOUT" "lean build of $f.lean" "$T/$f.log" $LEANC -o "build/$f.olean" "$here/$f.lean" \
    || { cat "$T/$f.log"; fail "build of $f.lean"; }
  if grep -n "declaration uses .sorry" "$T/$f.log"; then fail "sorry in $f.lean"; fi
  echo "$f.lean: $(( $(date +%s) - s )) s"
done

echo "== statements and axioms of the intermediate results"
# Types are compared with the text recorded when STATUS.txt was written, so a
# weakened statement fails.  (Definitions they use, e.g. runM / stepM / Rel in
# the proof files, are not pinned.)
{ echo "import ProofWrapper"
  echo "set_option pp.oneline false"
  echo "example : Utf8Boundary.printedWat = Utf8Wasm.printedWat := rfl"
  for t in Utf8Wasm.decoderModule_decodes Utf8Wasm.start_ok Utf8Wasm.done_runs Utf8Wasm.buffer_runs \
           Utf8Wasm.call_step Utf8Wasm.loop_correct Utf8Wasm.stepM_nil Utf8Wasm.stepM_enc \
           Utf8Wasm.runM_enc Utf8Wasm.buffer_ok Utf8Wasm.done_ok Utf8Pure.RefDecoder_correct \
           Utf8Wasm.shippedModuleCorrect_implies_v1 Utf8Wasm.decoderModule_pages Utf8Wasm.wrapperCallsCovered; do
    echo "#check @$t"; echo "#print axioms $t"; done
  # The pre-audit statement, shown implied by the current Boundary claim above.
  echo "#print Utf8Wasm.ShippedModuleCorrect_v1"; } > "$T/CheckPartial.lean"
limited "$STEP_TIMEOUT" "statement check" "$T/partial.txt" $LEANC "$T/CheckPartial.lean" || { cat "$T/partial.txt"; fail "statement check"; }
cat "$T/partial.txt"
# check.expected.txt holds the output recorded for the statements in STATUS.txt.
diff check.expected.txt "$T/partial.txt" || fail "statements or axioms of the intermediate results differ from check.expected.txt"
if grep -q sorryAx "$T/partial.txt"; then fail "sorryAx"; fi
echo "statements as recorded; every result depends only on (a subset of) [propext, Classical.choice, Quot.sound]"

echo "== top-level theorems: exactly the Boundary types, standard axioms only"
{ echo "import ProofWrapper"
  echo "example : Utf8Boundary.ShippedModuleCorrect := Utf8Wasm.shippedModuleCorrect"
  echo "example : Utf8Boundary.ShippedWrapperCovered := Utf8Wasm.shippedWrapperCovered"
  echo "#print axioms Utf8Wasm.shippedModuleCorrect"
  echo "#print axioms Utf8Wasm.shippedWrapperCovered"; } > "$T/CheckTop.lean"
limited "$STEP_TIMEOUT" "top-level check" "$T/top.txt" $LEANC "$T/CheckTop.lean" || { cat "$T/top.txt"; fail "Utf8Wasm.shippedModuleCorrect / shippedWrapperCovered do not have the Boundary types ShippedModuleCorrect / ShippedWrapperCovered"; }
cat "$T/top.txt"
[ "$(cat "$T/top.txt")" = "'Utf8Wasm.shippedModuleCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
'Utf8Wasm.shippedWrapperCovered' depends on axioms: [propext, Classical.choice, Quot.sound]" ] \
  || fail "axioms of Utf8Wasm.shippedModuleCorrect / shippedWrapperCovered are not exactly [propext, Classical.choice, Quot.sound]"

echo "== kernel replay of every non-core constant (Talos + candidate)"
# Re-checks, in a fresh kernel environment that imports only Init/Lean/Std, every
# constant the build left in the .olean files.  This does not trust the
# elaborator, so a declaration added by metaprogramming (macro/elab/addDecl,
# attributes) without kernel checking is caught; the forbidden-word grep cannot
# see those.  Lean's replay skips unsafe and partial constants (they cannot be
# used by a theorem).  Then checks that the replayed theorem has exactly the
# Boundary type (and the same for the non-vacuity theorem).
if [ "$SKIP_REPLAY" = yes ]; then
  echo "SKIPPED (--skip-replay)"; REPLAY_NOTE="kernel replay SKIPPED (--skip-replay)"
else
  cat > "$T/Replay.lean" <<'EOF'
import Lean
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let full ← importModules #[{module := `ProofWrapper}] {} (loadExts := false)
  let base ← importModules #[{module := `Init}, {module := `Lean}, {module := `Std}] {} (loadExts := false)
  let mut news : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in full.constants.map₁.toList do
    if !base.contains n then news := news.insert n ci
  for n in [`Utf8Wasm.shippedModuleCorrect, `Utf8Boundary.ShippedModuleCorrect,
            `Utf8Wasm.shippedWrapperCovered, `Utf8Boundary.ShippedWrapperCovered] do
    unless news.contains n do throw <| IO.userError s!"{n} not among the replayed constants"
  IO.println s!"replaying {news.size} non-core constants"
  let kenv ← base.toKernelEnv.replay news
  match kenv.find? `Utf8Wasm.shippedModuleCorrect with
  | some (.thmInfo t) =>
    unless t.type == .const `Utf8Boundary.ShippedModuleCorrect [] do
      throw <| IO.userError "replayed Utf8Wasm.shippedModuleCorrect does not have type Utf8Boundary.ShippedModuleCorrect"
  | _ => throw <| IO.userError "Utf8Wasm.shippedModuleCorrect is not a theorem in the replayed environment"
  match kenv.find? `Utf8Wasm.shippedWrapperCovered with
  | some (.thmInfo t) =>
    unless t.type == .const `Utf8Boundary.ShippedWrapperCovered [] do
      throw <| IO.userError "replayed Utf8Wasm.shippedWrapperCovered does not have type Utf8Boundary.ShippedWrapperCovered"
  | _ => throw <| IO.userError "Utf8Wasm.shippedWrapperCovered is not a theorem in the replayed environment"
  IO.println "replay OK"
EOF
  s=$(date +%s)
  limited "$REPLAY_TIMEOUT" "kernel replay" "$T/replay.txt" $LEANC --run "$T/Replay.lean" \
    || { cat "$T/replay.txt"; fail "kernel replay rejected the environment"; }
  cat "$T/replay.txt"
  [ "$(tail -1 "$T/replay.txt")" = "replay OK" ] || fail "kernel replay did not report OK"
  n=$(sed -n 's/^replaying \([0-9]*\) .*/\1/p' "$T/replay.txt")
  echo "kernel replay: $(( $(date +%s) - s )) s"
  REPLAY_NOTE="kernel replay of $n constants OK"
fi

echo "== difftest (on the shipped decoder.wasm checked above; started in the background)"
rc=0; wait "$DT_PID" || rc=$?; DT_PID=
[ "$rc" = 0 ] || { tail -20 "$T/dt.log"; fail "difftest (exit $rc)"; }
tail -5 "$T/dt.log"
grep -q '^RESULT: PASS' "$T/dt.log" || fail "difftest did not report RESULT: PASS"

cat <<'EOF'

NOT CHECKED (trusted): wasm-tools print/parse (the theorem is about the module
Talos decodes from the printed text, not about the bytes); Talos's semantics
and decoder, instantiation and validation (not modelled); the JS wrapper
decoder.mjs beyond its three LAYOUT constants (that it uses them as
Boundary's WrapperCallsCovered describes, never grows memory and passes back
only states the module returned is checked by reading) and the Wasm engine
(exercised only by the difftest harness).
EOF
echo "PASS: Utf8Boundary.ShippedModuleCorrect proved (Utf8Wasm.shippedModuleCorrect) and non-vacuity Utf8Boundary.ShippedWrapperCovered proved (Utf8Wasm.shippedWrapperCovered: every call the wrapper makes meets the guarantees' conditions), exact Boundary types, axioms [propext, Classical.choice, Quot.sound]; wrapper layout constants and memory size = Boundary's; shipped wasm = rebuild, printed text matches, clean build, Talos at pinned commit, $REPLAY_NOTE, difftest PASS"
