#!/bin/sh
set -eu
TASK_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
RIFFLE_TOOLCHAIN=${RIFFLE_TOOLCHAIN:-"$TASK_ROOT/../formalization/.tooling/lean-4.19.0-darwin_aarch64"}
RIFFLE_MATHLIB=${RIFFLE_MATHLIB:-"$TASK_ROOT/../formalization/.tooling/mathlib"}
RIFFLE_SEARCH="$TASK_ROOT/.lake/build/lib/lean:$TASK_ROOT/.lake/dependency-cache:$RIFFLE_MATHLIB/.lake/build/lib/lean"
for RIFFLE_PACKAGE in "$RIFFLE_MATHLIB"/.lake/packages/*; do
  if [ -d "$RIFFLE_PACKAGE/.lake/build/lib/lean" ]; then
    RIFFLE_SEARCH="$RIFFLE_SEARCH:$RIFFLE_PACKAGE/.lake/build/lib/lean"
  fi
done
export LEAN_PATH="$RIFFLE_SEARCH"
cd "$TASK_ROOT"
exec "$RIFFLE_TOOLCHAIN/bin/lean" "$@"
