#!/bin/sh
# Translate the safe core to LLBC then Lean. Run from spike/.
set -e
A=${AENEAS_BIN:-$HOME/aeneas-nightly/bin-x}
$A/charon cargo --preset=aeneas --exclude crate::shim --dest-file spike.llbc -- --lib
rm -f lean/Spike/*.lean
mkdir -p lean/Spike
$A/aeneas -backend lean -dest lean/Spike -split-files spike.llbc
