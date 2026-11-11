#!/bin/sh
# Build the Lean files against the prebuilt Aeneas library; outputs in build/.
# Usage: ./build.sh [file.lean ...]  (default: all, in dependency order).
# The pure layer must have been built first (build_pure.sh).
set -e
L=${AENEAS_LEAN:-$HOME/aeneas-nightly/lib/aeneas-lean}
HERE=$(cd "$(dirname "$0")" && pwd)
LP=$(cd "$L" && lake env printenv LEAN_PATH)
LEAN="elan run $(cat "$L/lean-toolchain") lean"
cd "$HERE"
files=${*:-"Decoder/Types.lean Decoder/Funs.lean Boundary.lean Proofs.lean Axioms.lean"}
mkdir -p build/Decoder
for f in $files; do
  m=${f%.lean}
  echo "== $m"
  if [ "$f" = Axioms.lean ]; then LEAN_PATH="$LP:$HERE/build" $LEAN $f; else
  LEAN_PATH="$LP:$HERE/build" $LEAN $f -o build/$m.olean -i build/$m.ilean; fi
done
