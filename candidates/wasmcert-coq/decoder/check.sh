#!/usr/bin/env bash
# Check of the WasmCert-Coq decoder candidate.  Boundary.v (hash-pinned
# below) states two top-level claims:
#   decoder_module_correct  -- proved as Decoder.Theorems.decoder_module_correct_proved
#   decoder_module_applies  -- proved as Decoder.NonVacuity.decoder_module_applies_proved
#     (the store made by instantiation meets the store condition of the first
#     claim, the largest 64 KiB call fits the layout, and instantiation has
#     exactly one possible result: the first claim is not vacuous for the
#     real module, and speaks about its real memory).
# For each, the script elaborates the theorem, by fully qualified name and with
# every quantifier explicit (@), against the claim's type, so a shadowing
# definition or an extra premise (a leaked section Hypothesis/Variable/Context)
# fails the check; Print Assumptions must equal the recorded list (WasmCert-Coq
# library axioms only; a top-level Hypothesis/Axiom would show up there); and
# rocqchk re-checks every compiled library of this development (decoder,
# symexec, determinism, pure layer) in the kernel; the installed libraries
# they build on (Stdlib, mathcomp, CompCert, coq-wasm) are loaded unchecked
# (FULL_ROCQCHK=1 re-checks those too, about 60 s more; SKIP_ROCQCHK=1 skips
# rocqchk; the verdict line says which was done).
# Boundary.v's call_returns includes the unique-outcome guarantee (no other
# result or trap reachable, no infinite run); it is proved from the
# determinism library ../determinism (built here, its main statements and
# fragment definition pinned in check.expected.txt) via DetInstance.v.
# The wrapper decoder.mjs: its LAYOUT line (IN, IN_MAX, OUT) must equal the
# values Rocq computes for Boundary.v's IN_addr, IN_max, OUT_addr, and the
# chunking loop, the copy and the output read must use those names (text check).
# Any failing step exits non-zero.
#
# Depends on (all rebuilt here from clean, so no stale .vo file counts):
# - the real pure layer in ../../pure-rocq: its .vo files are deleted and its
#   own check.sh is run (about 20 s; it must print ALL CHECKS PASSED);
# - the reusable symbolic-execution library ../symexec (depends only on
#   coq-wasm; about 5 s);
# - the determinism library ../determinism (depends only on coq-wasm; about 15 s).
set -euo pipefail
cd "$(dirname "$0")"
HERE=$(pwd)
CAND=$(cd "$HERE/../.." && pwd)
PURE=$CAND/pure-rocq
DET=$(cd "$HERE/../determinism" && pwd)
SYM=$(cd "$HERE/../symexec" && pwd)
SPEC=$CAND/spec-rocq/Utf8Laws.v
eval "$(opam env --switch=wasmcert 2>/dev/null)"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "FAIL: $*"; exit 1; }

SPEC_SHA=e5d72692cbe154feb46891bb914c6ee62dc27474ca2d6598afee99313f49eb75      # spec-rocq/Utf8Laws.v
BOUNDARY_SHA=2e8b73ec958c2386503517aefa79d92ebfc240bac1e02b5aed1ef46d8e4b42ed  # Boundary.v

echo "== reviewed files match their pinned hashes"
echo "$SPEC_SHA  $SPEC" | sha256sum -c - || fail "spec-rocq/Utf8Laws.v is not the audited spec"
echo "$BOUNDARY_SHA  Boundary.v" | sha256sum -c - || fail "Boundary.v differs from the reviewed version"

echo "== wrapper decoder.mjs: layout constants and their uses (text)"
# decoder.mjs declares the three layout constants on one line marked
# "// LAYOUT IN_addr IN_max OUT_addr"; their values are compared, after the
# build, with the values Rocq computes for Boundary.v's IN_addr, IN_max and
# OUT_addr (the last command of CheckTop.v below).  Here: that line exists once
# with plain decimals, the constants are used exactly at the expected places
# (the chunking loop steps by IN_MAX and cuts chunks with IN_MAX, the copy
# goes to IN, the output is read at OUT), and the code (comments removed)
# has no other declaration of these names and no other numeric literal >= 100.
[ "$(grep -c '// LAYOUT' decoder.mjs)" = 1 ] || fail "decoder.mjs must have exactly one '// LAYOUT' line"
LAYOUT_RE='^const IN = ([0-9]+), IN_MAX = ([0-9]+), OUT = ([0-9]+);  // LAYOUT IN_addr IN_max OUT_addr$'
JS_LAYOUT=$(sed -n -E "s|$LAYOUT_RE|\1 \2 \3|p" decoder.mjs)
[ -n "$JS_LAYOUT" ] || fail "decoder.mjs: the LAYOUT line is not 'const IN = <decimal>, IN_MAX = <decimal>, OUT = <decimal>;  // LAYOUT IN_addr IN_max OUT_addr'"
read -r JS_IN JS_IN_MAX JS_OUT <<< "$JS_LAYOUT"
need_line() {   # count fixed-text
  local n; n=$(grep -cF -- "$2" decoder.mjs || true)
  [ "$n" = "$1" ] || fail "decoder.mjs: expected $1 line(s) containing '$2', found $n"; }
need_line 1 'for (let p = 0; p < u8.length || p === 0; p += IN_MAX) {'
need_line 1 'const chunk = u8.subarray(p, Math.min(p + IN_MAX, u8.length));'
need_line 1 'mem.set(chunk, IN);'
need_line 1 'new Uint8Array(ex.memory.buffer, OUT, nbytes)'
JS_CODE=$(sed 's|//.*$||' decoder.mjs)
for w in IN:2 IN_MAX:3 OUT:2; do
  n=$(printf '%s\n' "$JS_CODE" | grep -oE "(^|[^A-Za-z0-9_\$.])${w%:*}([^A-Za-z0-9_\$]|\$)" | wc -l)
  [ "$n" = "${w#*:}" ] || fail "decoder.mjs: ${w%:*} occurs $n times in code, expected ${w#*:} (declaration + the uses checked above)"
done
if printf '%s\n' "$JS_CODE" | grep -v '^const IN = ' | grep -nE '(^|[^A-Za-z0-9_.])[0-9]{3,}'; then
  fail "decoder.mjs: numeric literal >= 100 outside the LAYOUT line"; fi
echo "decoder.mjs: IN=$JS_IN IN_MAX=$JS_IN_MAX OUT=$JS_OUT; chunking steps and cuts by IN_MAX, copies to IN, reads at OUT"

echo "== pure layer ../../pure-rocq: rebuilt from clean and checked by its own check.sh"
cmp "$SPEC" "$PURE/Utf8Laws.v" || fail "pure-rocq/Utf8Laws.v differs from the spec"
for f in $(sed -n 's/^\([A-Za-z0-9_]*\)\.v$/\1/p' "$PURE/_CoqProject"); do
  command rm -f "$PURE/$f.vo" "$PURE/$f.vok" "$PURE/$f.vos" "$PURE/$f.glob" "$PURE/.$f.aux"
done
"$PURE/check.sh" > "$T/pure.log" 2>&1 || { tail -30 "$T/pure.log"; fail "pure-rocq/check.sh"; }
grep '^ALL CHECKS PASSED' "$T/pure.log" || { tail -30 "$T/pure.log"; fail "pure-rocq/check.sh did not print ALL CHECKS PASSED"; }

echo "== checking for holes in the candidate's, ../symexec's and ../determinism's build files"
VFILES=$(sed -n 's/^\([A-Za-z0-9_]*\.v\)$/\1/p' _CoqProject)
DVFILES=$(sed -n 's/^\([A-Za-z0-9_]*\.v\)$/\1/p' "$DET/_CoqProject")
DVPATHS=$(for f in $DVFILES; do echo "$DET/$f"; done)
SVFILES=$(sed -n 's/^\([A-Za-z0-9_]*\.v\)$/\1/p' "$SYM/_CoqProject")
SVPATHS=$(for f in $SVFILES; do echo "$SYM/$f"; done)
# holes.pl (shared with pure-rocq/check.sh): Admitted, admit, Axiom(s),
# Parameter(s), Conjecture(s), Abort, Primitive, bypass_check, Admit
# Obligations, Typing Flags, Declare ML Module, Load, any Unset other than
# Strict Implicit / Printing Implicit Defensive (so Unset Guard/Positivity/
# Universe Checking, Local or not), and Hypothesis/Variable/Context outside a
# Section.  A second line of defence: Print Assumptions and rocqchk below are
# the semantic checks.
perl "$PURE/holes.pl" $VFILES $DVPATHS $SVPATHS || fail "proof holes or checker-weakening commands found"
echo "holes.pl: nothing found in: $VFILES"
echo "  nor in ../determinism: $DVFILES"
echo "  nor in ../symexec: $SVFILES"
grep -q '^-Q \.\./determinism Determinism$' _CoqProject || fail "_CoqProject does not map ../determinism to Determinism"
if grep -E '^-Q|^-R' "$DET/_CoqProject" | grep -v '^-Q \. Determinism$'; then
  fail "../determinism/_CoqProject has a load path other than itself (it must depend only on coq-wasm)"; fi
grep -q '^-Q \.\./symexec SymExec$' _CoqProject || fail "_CoqProject does not map ../symexec to SymExec"
if grep -E '^-Q|^-R' "$SYM/_CoqProject" | grep -v '^-Q \. SymExec$'; then
  fail "../symexec/_CoqProject has a load path other than itself (it must depend only on coq-wasm)"; fi

echo "== build ../symexec (clean: its .vo files are always rebuilt)"
for f in $SVFILES; do b=${f%.v}; command rm -f "$SYM/$b.vo" "$SYM/$b.vok" "$SYM/$b.vos" "$SYM/$b.glob" "$SYM/.$b.aux"; done
make -C "$SYM" all > "$T/symmake.log" 2>&1 || { cat "$T/symmake.log"; fail "make in ../symexec"; }
grep -E '^ROCQ compile' "$T/symmake.log" | tr '\n' ' '; echo

echo "== build ../determinism (clean: its .vo files are always rebuilt)"
for f in $DVFILES; do b=${f%.v}; command rm -f "$DET/$b.vo" "$DET/$b.vok" "$DET/$b.vos" "$DET/$b.glob" "$DET/.$b.aux"; done
make -C "$DET" all > "$T/detmake.log" 2>&1 || { cat "$T/detmake.log"; fail "make in ../determinism"; }
grep -E '^ROCQ compile' "$T/detmake.log" | tr '\n' ' '; echo

echo "== build (clean: candidate .vo files are always rebuilt, so no stale artefact counts)"
for f in $VFILES EmitHex.v; do b=${f%.v}; command rm -f "$b.vo" "$b.vok" "$b.vos" "$b.glob" ".$b.aux"; done
make all > "$T/make.log" 2>&1 || { cat "$T/make.log"; fail "make all"; }
grep -E '^ROCQ compile' "$T/make.log" | tr '\n' ' '; echo

echo "== decoder.wasm regenerated from the term must equal the shipped file"
command cp decoder.wasm "$T/shipped.wasm"
# decoder_hex.out is an intermediate (tracked for reference); regenerated below.
[ -f decoder_hex.out ] && command cp decoder_hex.out "$T/shipped_hex.out" || : > "$T/shipped_hex.out"
command rm -f decoder.wasm decoder_hex.out
if ! make decoder.wasm > "$T/emit.log" 2>&1; then
  cat "$T/emit.log"; command cp "$T/shipped.wasm" decoder.wasm; command cp "$T/shipped_hex.out" decoder_hex.out
  fail "make decoder.wasm"; fi
if ! cmp decoder.wasm "$T/shipped.wasm"; then
  command mv decoder.wasm decoder.wasm.regenerated
  command cp "$T/shipped.wasm" decoder.wasm; command cp "$T/shipped_hex.out" decoder_hex.out
  fail "shipped decoder.wasm differs from the bytes printed from decoder_module (kept as decoder.wasm.regenerated)"
fi
sha256sum decoder.wasm
echo "identical (Binary.v also proves decoder_bytes_parse_back: run_parse_module decoder_bytes = Some decoder_module)"

echo "== statements and assumptions"
# check.expected.txt holds the recorded output: the top-level theorem's type
# check against Boundary.v, the type of the conditional theorem, the definition
# of step_spec, the case lemmas, the decoder_bytes link, the determinism
# library's main statements and fragment definition (so a weakening of the
# fragment or of a lemma shows up here), and every Print Assumptions.
cat > "$T/CheckTop.v" <<'EOV'
From Decoder Require Import Boundary Binary Exports OutBound Decode Theorems StepEmpty StepPending StepComplete StepSpec DetInstance NonVacuity.
From Determinism Require Import Fragment ReduceDet Det Main.
(* The two top-level claims.  Fully qualified names (no shadowing) and every
   quantifier explicit (@, no implicit insertion): each Definition elaborates
   only if the theorem has exactly the claim's type, with no extra premise. *)
Definition top_correct_type : Prop :=
  forall (hfc : datatypes.host_function_class) (memory : memory.BlockUpdateMemory) (ho : host.host),
    @Decoder.Boundary.decoder_module_correct hfc memory ho.
Definition top_correct_check : top_correct_type := @Decoder.Theorems.decoder_module_correct_proved.
Definition top_applies_type : Prop :=
  forall (hfc : datatypes.host_function_class) (memory : memory.BlockUpdateMemory) (ho : host.host),
    @Decoder.Boundary.decoder_module_applies hfc memory ho.
Definition top_applies_check : top_applies_type := @Decoder.NonVacuity.decoder_module_applies_proved.
Locate decoder_module_correct_proved.
Locate decoder_module_applies_proved.
Locate decoder_module_correct.
Locate decoder_module_applies.
Check @Decoder.Theorems.decoder_module_correct_proved.
Check @Decoder.NonVacuity.decoder_module_applies_proved.
Print Assumptions top_correct_check.
Print Assumptions top_applies_check.
(* the output bound behind the layout (OutBound.v; pure) *)
Print pend.
Check step_out_bound.
Check decode_out_bound.
Check decode_out_area.
Check ref_done_out_bound.
Print Assumptions decode_out_bound.
Check step_spec_proved.
Check decoder_module_correct_if_step.
Check step_spec_of_cases.
Check step_case_empty.
Check step_case_reject.
Check step_case_extend.
Check step_case_complete2.
Check step_case_complete3.
Check step_case_complete4.
Check decoder_bytes_parse_back.
Print decoder_bytes.
Print step_spec.
Print writes.
Print Assumptions decoder_module_correct_if_step.
Print Assumptions decoder_bytes_parse_back.
Print Assumptions start_correct.
Print Assumptions done_correct.
Print Assumptions decode_correct.
Print Assumptions step_case_empty.
Print Assumptions step_case_reject.
Print Assumptions step_case_extend.
Print Assumptions step_case_complete2.
Print Assumptions step_case_complete3.
Print Assumptions step_case_complete4.
(* determinism library: statements and the fragment, pinned by content *)
Check reduce_det_fragment_proved.
Print reduce_det_fragment.
Check fragment_deterministic_outcome.
Print deterministic_outcome.
Check still_reaches_stuck_is_target.
Print cfg_ok.
Print funcs_ok.
Print func_ok.
Print es_ok.
Print ai_ok.
Print bi_ok.
Print int_type.
Check decoder_call_outcome.
Print Assumptions decoder_call_outcome.
(* layout constants (IN_addr, IN_max, OUT_addr), compared with decoder.mjs's
   LAYOUT line by check.sh; must stay the last command of this file *)
Eval vm_compute in (BinNat.N.to_nat Decoder.Boundary.IN_addr, Decoder.Boundary.IN_max, BinNat.N.to_nat Decoder.Boundary.OUT_addr).
EOV
rocq c -Q . Decoder -Q "$PURE" Utf8 -Q "$DET" Determinism -Q "$SYM" SymExec "$T/CheckTop.v" > "$T/assum.raw" 2>&1 || { cat "$T/assum.raw"; fail "statement check"; }
grep -v 'Running as root' "$T/assum.raw" > "$T/assum.txt" || true
cat "$T/assum.txt"
diff check.expected.txt "$T/assum.txt" || fail "statements or assumptions differ from check.expected.txt"
echo "statements, step_spec and assumptions as recorded"

echo "== wrapper layout constants = the values Rocq computes for Boundary.v's layout"
# Compared with the wrapper even though the pin above already fixes the values:
# a change to Module.v with the pin updated still fails here.
ROCQ_LAYOUT=$(tail -2 "$T/assum.txt" | sed -n -E 's/^     = \(([0-9]+), ([0-9]+), ([0-9]+)\)$/\1 \2 \3/p')
[ "$(tail -1 "$T/assum.txt")" = '     : nat * nat * nat' ] && [ -n "$ROCQ_LAYOUT" ] \
  || fail "CheckTop.v: last output is not '= (<IN_addr>, <IN_max>, <OUT_addr>) : nat * nat * nat'"
read -r R_IN R_IN_MAX R_OUT <<< "$ROCQ_LAYOUT"
[ "$JS_IN" = "$R_IN" ] || fail "layout: decoder.mjs IN = $JS_IN, Boundary.IN_addr = $R_IN"
[ "$JS_IN_MAX" = "$R_IN_MAX" ] || fail "layout: decoder.mjs IN_MAX = $JS_IN_MAX, Boundary.IN_max = $R_IN_MAX"
[ "$JS_OUT" = "$R_OUT" ] || fail "layout: decoder.mjs OUT = $JS_OUT, Boundary.OUT_addr = $R_OUT"
echo "IN = IN_addr = $R_IN, IN_MAX = IN_max = $R_IN_MAX, OUT = OUT_addr = $R_OUT"

if [ "${SKIP_ROCQCHK:-0}" = 1 ]; then
  ROCQCHK_NOTE="rocqchk SKIPPED (SKIP_ROCQCHK=1)"
  echo "== rocqchk: SKIPPED (SKIP_ROCQCHK=1)"
else
  LP=(-Q . Decoder -Q "$PURE" Utf8 -Q "$DET" Determinism -Q "$SYM" SymExec)
  if [ "${FULL_ROCQCHK:-0}" = 1 ]; then
    echo "== rocqchk: kernel re-check of the top-level libraries and ALL their dependencies"
    rocqchk "${LP[@]}" Decoder.Theorems Decoder.NonVacuity Determinism.Main > "$T/chk.log" 2>&1 \
      || { tail -30 "$T/chk.log"; fail "rocqchk"; }
    ROCQCHK_NOTE="rocqchk passed (all libraries, including installed dependencies)"
  else
    echo "== rocqchk: kernel re-check of every library of this development (installed dependencies loaded unchecked)"
    MODS=""
    for f in $VFILES; do MODS="$MODS -norec Decoder.${f%.v}"; done
    for f in $SVFILES; do MODS="$MODS -norec SymExec.${f%.v}"; done
    for f in $DVFILES; do MODS="$MODS -norec Determinism.${f%.v}"; done
    for f in $(sed -n 's/^\([A-Za-z0-9_]*\)\.v$/\1/p' "$PURE/_CoqProject"); do MODS="$MODS -norec Utf8.$f"; done
    rocqchk "${LP[@]}" $MODS > "$T/chk.log" 2>&1 || { tail -30 "$T/chk.log"; fail "rocqchk"; }
    ROCQCHK_NOTE="rocqchk passed (every library of this development; installed dependencies not re-checked)"
  fi
  grep -q 'Modules were successfully checked' "$T/chk.log" || { tail -30 "$T/chk.log"; fail "rocqchk did not report success"; }
  echo "$ROCQCHK_NOTE"
fi

echo "== difftest harness (on the shipped decoder.wasm checked above)"
node "$CAND/difftest/run.mjs" "$HERE/decoder.mjs" > "$T/dt.log" 2>&1 || { tail -20 "$T/dt.log"; fail difftest; }
tail -5 "$T/dt.log"
grep -q '^RESULT: PASS' "$T/dt.log" || fail "difftest did not report RESULT: PASS"

cat <<'EOF'

NOT CHECKED (trusted or not proved): WasmCert-Coq's semantics, its binary
printer binary_of_module (the parser direction is checked by
decoder_bytes_parse_back) and its library axioms (listed above);
the hex-to-bytes step in the Makefile (node); the JS wrapper decoder.mjs
beyond its layout constants and their textual uses (checked above) and the
Wasm engine (exercised only by the difftest harness).
EOF
echo "PASS: decoder_module_correct (Boundary.v) proved unconditionally, including the unique-outcome guarantee for every call (no trap or other result reachable, no infinite run); decoder_module_applies proved (the instantiated module's fixed 5-page memory meets the store condition, the largest 64 KiB call fits, and instantiation has exactly one result, so the guarantees are not vacuous and are about the real memory); assumptions = WasmCert-Coq library axioms as recorded; $ROCQCHK_NOTE; shipped wasm = bytes printed from the term; wrapper layout constants = Boundary.v layout; difftest PASS"
