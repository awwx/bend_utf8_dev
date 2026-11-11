#!/bin/sh
# Translate the safe core to LLBC then Lean.  Usage: ./charon.sh OUTDIR [TARGET]
# Writes OUTDIR/decoder.llbc and OUTDIR/Decoder/{Types,Funs}.lean.
set -e
export PATH=$HOME/.cargo/bin:$PATH
A=${AENEAS_BIN:-$HOME/aeneas-nightly/bin-x}
OUT=$1; TGT=$2
cd "$(dirname "$0")"
mkdir -p "$OUT/Decoder"
if [ -n "$TGT" ]; then TA="--target $TGT"; else TA=""; fi
$A/charon cargo --preset=aeneas --exclude crate::shim --dest-file "$OUT/decoder.llbc" -- --lib $TA
rm -f "$OUT"/Decoder/*.lean
$A/aeneas -backend lean -dest "$OUT/Decoder" -split-files "$OUT/decoder.llbc"
