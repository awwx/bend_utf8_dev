#!/usr/bin/env bash
# Rebuild proof sources in a fresh directory and independently replay the kernel.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/.." && pwd)
TC=$(cat "$HERE/lean-toolchain")
TALOS=$ROOT/candidates/talos/talos
WT=$ROOT/candidates/talos/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools
COMMIT=d7c84ac660757953b752bdfc9cb8dae3dab623ed
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
SKIP_REPLAY=no
case "${1:-}" in
  '') ;;
  --skip-replay) SKIP_REPLAY=yes ;;
  *) echo 'Usage: ./check.sh [--skip-replay]'; exit 2 ;;
esac
[ "$(git -C "$TALOS" rev-parse HEAD)" = "$COMMIT" ]
[ -z "$(git -C "$TALOS" status --porcelain --untracked-files=all)" ]
[ "$(cat "$TALOS/lean-toolchain")" = "$TC" ]
"$WT" --version
elan run "$TC" lean --version
node --version
"$WT" parse "$HERE/prefix.wat" -o "$T/raw.wasm"
"$WT" strip --all "$T/raw.wasm" -o "$T/prefix.wasm"
cmp "$T/prefix.wasm" "$HERE/prefix.wasm"
"$WT" validate "$T/prefix.wasm"
"$WT" print "$T/prefix.wasm" > "$T/prefix.printed.wat"
cmp "$T/prefix.printed.wat" "$HERE/prefix.printed.wat"
sha256sum "$HERE/prefix.wasm" "$HERE/prefix.printed.wat"
command cp "$ROOT/candidates/spec-lean/Utf8Laws.lean" "$T/"
for f in Utf8Bits Utf8Ref Utf8Table Utf8Proofs; do
  command cp "$ROOT/candidates/pure-lean/$f.lean" "$T/"
done
command cp "$ROOT/copier/Utf8Roundtrip.lean" "$ROOT/copier/StreamModel.lean" "$T/"
command cp "$HERE/"*.lean "$T/"
# Obtain a topological order for project-local imports; imported Talos modules
# remain at the pinned checkout, whose build freshness is checked below.
python3 - "$T" <<'PY' > "$T/order"
import pathlib, re, sys
root = pathlib.Path(sys.argv[1])
files = {p.stem: p for p in root.glob('*.lean') if p.stem not in ('Replay', 'Audit')}
seen = set()
def visit(name):
    if name in seen: return
    seen.add(name)
    for dep in re.findall(r'^import\s+(\w+)', files[name].read_text(), re.M):
        if dep in files: visit(dep)
    print(name)
for name in sorted(files): visit(name)
PY
FORBID='\b(sorry|admit|axiom|native_decide|implemented_by|unsafe|opaque|skipKernelTC)\b|@\[[^]]*\bextern\b|#exit|set_option +debug\.'
while read -r f; do
  if grep -nE "$FORBID" "$T/$f.lean"; then echo "FAIL: forbidden construct in $f"; exit 1; fi
  if grep -nE '^[^-]*\bbv_decide\b' "$T/$f.lean"; then exit 1; fi
done < "$T/order"
MODS=$(sed -n 's/^import \(Interpreter\.[A-Za-z0-9_.]*\).*/\1/p' "$T/"*.lean | sort -u)
(cd "$TALOS/interpreter" && lake build --no-build $MODS)
export LEAN_PATH="$T:$(cd "$TALOS/interpreter" && lake env printenv LEAN_PATH)"
cd "$T"
while read -r f; do
  echo "Checking $f"
  timeout --kill-after=20 "${CHECK_STEP_TIMEOUT:-900}" elan run "$TC" lean -o "$T/$f.olean" "$T/$f.lean"
done < "$T/order"
# Audit.lean fixes the final theorem types and their expected trust footprint.
elan run "$TC" lean "$HERE/Audit.lean" > "$T/axioms.txt"
cat "$T/axioms.txt"
python3 - "$T/axioms.txt" <<'PY'
import pathlib, re, sys
text = pathlib.Path(sys.argv[1]).read_text()
assert len(re.findall(r'depends on axioms|does not depend', text)) == 8, text
for names in re.findall(r'depends on axioms:\s*\[([^]]*)\]', text):
    assert set(names.replace(' ', '').replace('\n', '').split(',')) <= {'propext', 'Classical.choice', 'Quot.sound'}, names
assert 'sorryAx' not in text
PY
if [ "$SKIP_REPLAY" = no ]; then
  timeout --kill-after=20 "${CHECK_REPLAY_TIMEOUT:-1500}" elan run "$TC" lean --run "$HERE/Replay.lean"
else
  echo 'WARNING: independent kernel replay SKIPPED'
fi
node "$HERE/test.mjs"
if [ "$SKIP_REPLAY" = no ]; then
  echo 'ALL LINE-PREFIX CHECKS PASSED (independent kernel replay included)'
else
  echo 'LINE-PREFIX CHECKS PASSED EXCEPT INDEPENDENT KERNEL REPLAY (SKIPPED)'
fi
