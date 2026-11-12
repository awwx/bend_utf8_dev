#!/usr/bin/env bash
# Full check of the Aeneas decoder candidate.
# Usage: ./check.sh [--fast] [--refresh-copies] [--skip-replay]
#   --fast: reuse the pure-layer .olean files in lean/build only if they were
#           built from exactly the current pure-layer sources (sha256 stamp),
#           and run the difftest harness with --no-huge.
#   --refresh-copies: copy pure-lean/*.lean over stale lean/pure/ copies
#           (without it a stale copy is a FAIL; nothing is overwritten silently).
#   --skip-replay: skip the kernel replay (step 6b; about 1.5 min, 7 GB RAM); the
#           final line then says "kernel replay SKIPPED".  A result counts only
#           from a run with the replay.
# CHECK_REPLAY_TIMEOUT (seconds, default 900): the replay is killed and the check
# FAILs if it runs longer.
# Prints "=== ALL CHECKS PASSED" only if every step succeeded; any failure
# exits non-zero.  What this script does NOT check is printed at the end.
set -euo pipefail
cd "$(dirname "$0")"
HERE=$(pwd)
CAND=$(cd "$HERE/../.." && pwd)        # .../candidates, located from this script's path
export PATH=$HOME/.cargo/bin:$PATH
FAST=; REFRESH=no; SKIP_REPLAY=no
for a in "$@"; do
  case $a in
    --fast) FAST=--fast ;;
    --refresh-copies) REFRESH=yes ;;
    --skip-replay) SKIP_REPLAY=yes ;;
    *) echo "usage: $0 [--fast] [--refresh-copies] [--skip-replay]"; exit 2 ;;
  esac
done
REPLAY_TIMEOUT=${CHECK_REPLAY_TIMEOUT:-900}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
t0=$(date +%s)
step() { echo; echo "=== $* ($(( $(date +%s) - t0 ))s)"; }
fail() { echo "FAIL: $*"; exit 1; }

# Pinned hashes of the two reviewed files.  If either is edited on purpose,
# the reviewer must re-read it and update the hash here.
SPEC_SHA=29396a7e1f013ee5a8cee9b3fb94a186e0f809bd68717f7b3046508cfe3b0583      # spec-lean/Utf8Laws.lean
BOUNDARY_SHA=f6750a531047f458c30831baa2d7b1667ab55ef5dc610c1d00dc63575d342fdc  # lean/Boundary.lean
PURE_FILES="Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs Utf8StepFacts"

step "0. reviewed files match their pinned hashes"
echo "$SPEC_SHA  $CAND/spec-lean/Utf8Laws.lean" | sha256sum -c - || fail "spec-lean/Utf8Laws.lean is not the audited spec"
echo "$BOUNDARY_SHA  lean/Boundary.lean" | sha256sum -c - || fail "lean/Boundary.lean differs from the reviewed version"

step "0b. wrapper constants: decoder.mjs and the shim (src/lib.rs) agree with lean/Boundary.lean"
# The non-vacuity statement Boundary.VerifiedForWrapper is about the call sizes below.
failc() { echo "FAIL: $*" >&2; exit 1; }   # for use inside $(...): message to stderr
# Lean side: one clearly marked line each in Boundary.lean (decimal literals).
lean_const() {
  local v; v=$(sed -nE "s/^def $1 : Nat := ([0-9]+)\$/\1/p" lean/Boundary.lean)
  [ "$(printf '%s\n' "$v" | grep -c .)" = 1 ] || failc "lean/Boundary.lean: no single line 'def $1 : Nat := <number>'"
  echo "$v"
}
# JS side: the line 'const NAME = <expr>;' at the top level of decoder.mjs; <expr> may use
# only digits, earlier constants, + * << and parentheses, and is evaluated by bash.
js_const() {
  local e; e=$(sed -nE "s/^const $1 = ([^;]+);.*\$/\1/p" decoder.mjs)
  [ "$(printf '%s\n' "$e" | grep -c .)" = 1 ] || failc "decoder.mjs: no single line 'const $1 = <expr>;'"
  printf '%s\n' "$e" | grep -qE '^[0-9A-Z_ *+<()]+$' || failc "decoder.mjs: const $1 = '$e' is not a plain constant expression"
  echo $(( e ))
}
# Lines of the wrapper and the shim that the statement's comment describes must be present
# verbatim, the given number of times (call sites, lengths passed, state round trip, layout).
need_line() {   # file count text [name of file in messages]
  local n; n=$(grep -cF -- "$3" "$1" || true)
  [ "$n" = "$2" ] || fail "${4:-$1}: expected $2 line(s) containing '$3', found $n"
}
CHUNK=$(js_const CHUNK); OUT_CAP=$(js_const OUT_CAP)
L_CHUNK=$(lean_const MaxChunkBytes); L_OUT=$(lean_const OutCapacity)
echo "decoder.mjs: CHUNK=$CHUNK OUT_CAP=$OUT_CAP;  Boundary.lean: MaxChunkBytes=$L_CHUNK OutCapacity=$L_OUT"
[ "$CHUNK" = "$L_CHUNK" ] || fail "CHUNK in decoder.mjs ($CHUNK) differs from Boundary.MaxChunkBytes ($L_CHUNK)"
[ "$OUT_CAP" = "$L_OUT" ] || fail "OUT_CAP in decoder.mjs ($OUT_CAP) differs from Boundary.OutCapacity ($L_OUT)"
M=decoder.mjs
need_line $M 1 'for (let off = 0; off < buf.length || (off === 0 && parts.length === 0); off += CHUNK) {'
need_line $M 1 'const len = Math.min(CHUNK, buf.length - off);'
need_line $M 1 'utf8_decode_buffer('
need_line $M 1 'const k = x.utf8_decode_buffer(st, IN, len, OUT, OUT_CAP, ST) >>> 0;'
need_line $M 1 'st = new Uint32Array(mem(), ST, 1)[0];'
need_line $M 1 'utf8_decode_done('
need_line $M 1 'const k = x.utf8_decode_done(state >>> 0, OUT, OUT_CAP) >>> 0;'
need_line $M 1 'const need = CHUNK + 4 * OUT_CAP + 4;'
need_line $M 1 'const base = x.memory.grow(Math.ceil(need / PAGE)) * PAGE;'
need_line $M 1 'const IN = base, OUT = base + CHUNK, ST = OUT + 4 * OUT_CAP;'
need_line $M 1 'const PAGE = 65536;'
S=$T/shim.rs
sed -n '/^mod shim {/,/^}/p' src/lib.rs > "$S"
[ -s "$S" ] || fail "src/lib.rs: no 'mod shim { ... }' block"
need_line "$S" 1 'super::decode_start_state()' "src/lib.rs (mod shim)"
need_line "$S" 1 'let input = core::slice::from_raw_parts(in_ptr, in_len);' "src/lib.rs (mod shim)"
need_line "$S" 2 'let out = core::slice::from_raw_parts_mut(out_ptr, out_len);' "src/lib.rs (mod shim)"
need_line "$S" 1 'let (s, k) = super::decode_buffer(state, input, out);' "src/lib.rs (mod shim)"
need_line "$S" 1 '*state_out = s;' "src/lib.rs (mod shim)"
need_line "$S" 1 'super::decode_done(state, out)' "src/lib.rs (mod shim)"
need_line "$S" 0 'static' "src/lib.rs (mod shim)"      # the shim has no buffers of its own; sizes come from the wrapper
echo "constants agree; wrapper call lines and shim slice/state lines as described in Boundary.lean"

step "1. spec and pure layer: build copies equal the audited spec / pure-lean sources"
cmp "$CAND/spec-lean/Utf8Laws.lean" "$CAND/pure-lean/Utf8Laws.lean" \
  || fail "pure-lean/Utf8Laws.lean differs from spec-lean/Utf8Laws.lean"
for f in $PURE_FILES; do
  if ! cmp -s "$CAND/pure-lean/$f.lean" "lean/pure/$f.lean"; then
    if [ "$REFRESH" = yes ]; then
      echo "note: lean/pure/$f.lean was stale; refreshing it from pure-lean/ (--refresh-copies)"
      command cp "$CAND/pure-lean/$f.lean" "lean/pure/$f.lean"
    else
      diff "$CAND/pure-lean/$f.lean" "lean/pure/$f.lean" | head -20 || true
      fail "lean/pure/$f.lean differs from pure-lean/$f.lean (rerun with --refresh-copies to copy pure-lean/ over it)"
    fi
  fi
done
# The files the build reads (lean/pure/*) are compared with the independent
# sources; the spec copy also with the pinned spec.
for f in $PURE_FILES; do cmp "$CAND/pure-lean/$f.lean" "lean/pure/$f.lean" || fail "lean/pure/$f.lean differs from pure-lean/$f.lean"; done
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
-- Realizes is still exactly the reviewed formula (its body now has the name RealizesWith).
open Aeneas Aeneas.Std Result in
example (D : Decoder) : Boundary.Realizes D = (∃ R : D.State → U32 → Prop,
    (∃ v, decoder.decode_start_state = ok v ∧ R D.start v) ∧
    (∀ (s : D.State) (v : U32) (input : Slice U8) (out : Slice U32),
      R s v → 2 * input.length ≤ out.length →
      ∃ (v' : U32) (k : Usize) (out' : Slice U32),
        decoder.decode_buffer v input out = ok ((v', k), out') ∧
        R (D.decode_buffer s (Boundary.bytes input)).1 v' ∧
        Boundary.WritesText out out' k (D.decode_buffer s (Boundary.bytes input)).2) ∧
    (∀ (s : D.State) (v : U32) (out : Slice U32),
      R s v → 1 ≤ out.length →
      ∃ (k : Usize) (out' : Slice U32),
        decoder.decode_done v out = ok (k, out') ∧
        Boundary.WritesText out out' k (D.decode_done s))) := rfl
-- The non-vacuity theorem has exactly the type of the reviewed wrapper claim.
example : Boundary.VerifiedForWrapper := DecoderProofs.verified_for_wrapper
example : Boundary.VerifiedForWrapper = (∃ D : Decoder, D.Correct ∧ ∃ R : D.State → Aeneas.Std.U32 → Prop,
    Boundary.RealizesWith D R ∧ Boundary.CountsBounded D R ∧ Boundary.WrapperCallsCovered D R ∧
    Boundary.WrapperLayoutFits) := rfl
#print axioms DecoderProofs.verified
#print axioms DecoderProofs.verified_for_wrapper
#print axioms DecoderProofs.realizes
#print axioms Utf8Pure.RefDecoder_correct
EOF
cat > "$T/expected_axioms.txt" <<'EOF'
'DecoderProofs.verified' depends on axioms: [propext, Classical.choice, Quot.sound]
'DecoderProofs.verified_for_wrapper' depends on axioms: [propext, Classical.choice, Quot.sound]
'DecoderProofs.realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Utf8Pure.RefDecoder_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF
L=${AENEAS_LEAN:-$HOME/aeneas-nightly/lib/aeneas-lean}
LP=$(cd "$L" && lake env printenv LEAN_PATH)
(cd lean && LEAN_PATH="$LP:$HERE/lean/build" elan run "$(cat "$L/lean-toolchain")" lean "$T/CheckTop.lean") \
  > "$T/axioms.txt" 2>&1 || { cat "$T/axioms.txt"; fail "top-level statement check"; }
cat "$T/axioms.txt"
diff "$T/expected_axioms.txt" "$T/axioms.txt" || fail "axiom output differs from the expected list"
echo "DecoderProofs.verified : Boundary.Verified; DecoderProofs.verified_for_wrapper : Boundary.VerifiedForWrapper; axioms exactly as expected"

step "6b. kernel replay of everything Proofs imports except Lean core (candidate, pure layer, Aeneas library, and the Mathlib/Batteries/Aesop/... modules it imports)"
# Re-checks with the kernel, in a fresh environment that imports only Init/Lean/Std,
# every other constant in the import closure of Proofs (read from the .olean files).
# This does not trust the elaborator: a declaration added by metaprogramming without
# kernel checking (e.g. addDecl under debug.skipKernelTC set from an elab, with the
# option name built from strings) passes steps 4 and 6 but is rejected here.  Lean's
# replay skips unsafe and partial constants (a theorem cannot use them).  Then checks
# on the replayed environment that the two theorems have exactly the Boundary types
# and, recomputed there from the replayed constants, exactly the three standard
# axioms.  (The Aeneas library itself declares bv_decide axioms such as
# ..._native.bv_decide.ax_*; they are replayed as axioms and must not be used.)
if [ "$SKIP_REPLAY" = yes ]; then
  echo "SKIPPED (--skip-replay)"; REPLAY_NOTE="kernel replay SKIPPED (--skip-replay)"
else
  cat > "$T/Replay.lean" <<'EOF'
import Lean
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let full ← importModules #[{module := `Proofs}] {} (loadExts := false)
  let base ← importModules #[{module := `Init}, {module := `Lean}, {module := `Std}] {} (loadExts := false)
  let mut news : Std.HashMap Name ConstantInfo := {}
  let mut roots : Std.HashSet Name := {}
  for (n, ci) in full.constants.map₁.toList do
    if !base.contains n then
      news := news.insert n ci
      if let some i := full.getModuleIdxFor? n then
        roots := roots.insert (full.header.moduleNames[i.toNat]!).getRoot
  for n in [`DecoderProofs.verified, `Boundary.Verified,
            `DecoderProofs.verified_for_wrapper, `Boundary.VerifiedForWrapper] do
    unless news.contains n do throw <| IO.userError s!"{n} not among the replayed constants"
  let rs := roots.toArray.map (·.toString) |>.qsort (· < ·)
  IO.println s!"replaying {news.size} constants of {full.header.moduleNames.size} modules (all but Init/Lean/Std); module roots {rs.toList}"
  let kenv ← base.toKernelEnv.replay news
  match kenv.find? `DecoderProofs.verified with
  | some (.thmInfo t) =>
    unless t.type == .const `Boundary.Verified [] do
      throw <| IO.userError "replayed DecoderProofs.verified does not have type Boundary.Verified"
  | _ => throw <| IO.userError "DecoderProofs.verified is not a theorem in the replayed environment"
  match kenv.find? `DecoderProofs.verified_for_wrapper with
  | some (.thmInfo t) =>
    unless t.type == .const `Boundary.VerifiedForWrapper [] do
      throw <| IO.userError "replayed DecoderProofs.verified_for_wrapper does not have type Boundary.VerifiedForWrapper"
  | _ => throw <| IO.userError "DecoderProofs.verified_for_wrapper is not a theorem in the replayed environment"
  -- Axioms of the two theorems, recomputed by walking the replayed kernel constants
  -- (#print axioms in step 6 uses per-module axiom lists stored in the .olean files).
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
  for c in [`DecoderProofs.verified, `DecoderProofs.verified_for_wrapper] do
    match axiomsOf c with
    | .error e => throw <| IO.userError e
    | .ok axs =>
      IO.println s!"replayed {c} depends on axioms: {axs.toList}"
      unless axs == #[`Classical.choice, `Quot.sound, `propext].qsort Name.lt do
        throw <| IO.userError s!"replayed {c}: axioms are not exactly [propext, Classical.choice, Quot.sound]"
  IO.println "replay OK"
EOF
  s=$(date +%s); rc=0
  (cd lean && LEAN_PATH="$LP:$HERE/lean/build" timeout --kill-after=20 "$REPLAY_TIMEOUT" \
     elan run "$(cat "$L/lean-toolchain")" lean --run "$T/Replay.lean") > "$T/replay.txt" 2>&1 || rc=$?
  if [ "$rc" = 124 ] || [ "$rc" = 137 ]; then
    tail -20 "$T/replay.txt"; fail "TIMEOUT: kernel replay did not finish within $REPLAY_TIMEOUT s (killed)"; fi
  cat "$T/replay.txt"
  [ "$rc" = 0 ] || fail "kernel replay rejected the environment"
  [ "$(tail -1 "$T/replay.txt")" = "replay OK" ] || fail "kernel replay did not report OK"
  n=$(sed -n 's/^replaying \([0-9]*\) .*/\1/p' "$T/replay.txt")
  echo "kernel replay: $(( $(date +%s) - s )) s"
  REPLAY_NOTE="kernel replay OK ($n constants: all of Proofs' imports except Lean core Init/Lean/Std)"
fi

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
the difftest harness; step 0b only checks that their call sizes and call lines are
the ones Boundary.VerifiedForWrapper is about -- that the shim's raw pointers give
slices of those lengths over memory the wrapper really reserved is not proved);
the Wasm engine.  The kernel replay (step 6b) covers every constant imported by
Proofs except Lean core (Init/Lean/Std, which the replaying kernel itself is built
on); it does not cover lean/Axioms.lean (not imported by Proofs; a report only) or
unsafe/partial constants (skipped by Lean's replay; a theorem cannot use them).
EOF
step "ALL CHECKS PASSED: Boundary.Verified, and non-vacuity for the wrapper's calls (Boundary.VerifiedForWrapper); $REPLAY_NOTE"
