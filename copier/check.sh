#!/usr/bin/env bash
set -euo pipefail

if (( $# > 0 )) && [[ $# != 1 || $1 != --paranoid ]]; then
  echo "usage: $0 [--paranoid]" >&2
  exit 2
fi
if [[ $(id -u) == 0 ]]; then
  echo "Run this checker as a non-root user: comparator's sandbox must not run privileged." >&2
  exit 2
fi
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

# Make the spec sources available inside comparator's project sandbox.
mkdir -p -- ./spec
command cp -- ../lean/spec/Utf8Laws.lean ../lean/spec/Utf8Check.lean ./spec/
exec elan run "$(cat lean-toolchain)" lake comparator "$@"
