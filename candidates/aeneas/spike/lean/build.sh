#!/bin/sh
# Build the Lean files of the spike against the prebuilt Aeneas library.
# Usage: ./build.sh [Module ...]   (default: all, in dependency order)
set -e
L=${AENEAS_LEAN:-$HOME/aeneas-nightly/lib/aeneas-lean}
HERE=$(cd "$(dirname "$0")" && pwd)
LP=$(cd "$L" && lake env printenv LEAN_PATH)
LEAN="elan run $(cat "$L/lean-toolchain") lean"
cd "$HERE"
mods=${*:-"Types Funs Spec Proofs"}
for m in $mods; do
  echo "== Spike.$m"
  LEAN_PATH="$LP:$HERE/build" $LEAN Spike/$m.lean -o build/Spike/$m.olean -i build/Spike/$m.ilean
done
