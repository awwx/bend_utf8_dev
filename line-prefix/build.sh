#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
WT=../candidates/talos/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
"$WT" parse prefix.wat -o "$T/raw.wasm"
"$WT" strip --all "$T/raw.wasm" -o prefix.wasm
"$WT" validate prefix.wasm
"$WT" print prefix.wasm > prefix.printed.wat
sha256sum prefix.wasm prefix.printed.wat
