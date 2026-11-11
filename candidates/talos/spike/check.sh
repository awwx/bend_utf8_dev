#!/usr/bin/env bash
# Rebuild spike.wasm, re-derive the text the Lean proofs read, check proofs, run Node tests.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
WT=$here/../tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools
cd "$here"
$WT parse spike.wat -o spike.unstripped.wasm
$WT strip --all -o spike.wasm spike.unstripped.wasm
rm -f spike.unstripped.wasm
$WT validate spike.wasm
$WT print spike.wasm > spike.printed.wat.new
if ! cmp -s spike.printed.wat spike.printed.wat.new; then
  echo "spike.printed.wat is stale: wasm-tools print spike.wasm differs"; diff spike.printed.wat spike.printed.wat.new; exit 1
fi
rm -f spike.printed.wat.new
sha256sum spike.wasm spike.printed.wat
export LEAN_PATH=$(cd ../talos/interpreter && lake env printenv LEAN_PATH)
time lean "$here/Spike.lean"
node test.mjs
