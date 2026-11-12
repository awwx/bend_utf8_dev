#!/bin/sh
# Build the shared pure layer (copied unmodified) with the Aeneas Lean toolchain into build/.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
L=${AENEAS_LEAN:-$HOME/aeneas-nightly/lib/aeneas-lean}
LEAN="elan run $(cat "$L/lean-toolchain") lean"
mkdir -p "$HERE/build"
cd "$HERE/pure"
for f in Utf8Laws Utf8Bits Utf8Ref Utf8Table Utf8Proofs; do
  echo "== pure $f"; LEAN_PATH="$HERE/build" $LEAN $f.lean -o "$HERE/build/$f.olean" -i "$HERE/build/$f.ilean"
done
