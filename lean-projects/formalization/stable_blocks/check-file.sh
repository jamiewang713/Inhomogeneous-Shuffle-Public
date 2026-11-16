#!/bin/sh
set -eu
TASK_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TASK_LEAN="$TASK_ROOT/.tooling/lean-4.19.0-darwin_aarch64/bin/lean"
if [ ! -x "$TASK_LEAN" ]; then TASK_LEAN=$(command -v lean); fi
TASK_MATHLIB="$TASK_ROOT/.tooling/mathlib"
if [ ! -d "$TASK_MATHLIB" ]; then TASK_MATHLIB="$TASK_ROOT/.lake/packages/mathlib"; fi
TASK_PACKAGES="$TASK_MATHLIB/.lake/packages"
if [ ! -d "$TASK_PACKAGES" ]; then TASK_PACKAGES="$TASK_ROOT/.lake/packages"; fi
TASK_PATH="$TASK_ROOT:$TASK_MATHLIB/.lake/build/lib/lean"
for TASK_PACKAGE in "$TASK_PACKAGES"/*; do
  TASK_PATH="$TASK_PATH:$TASK_PACKAGE/.lake/build/lib/lean"
done
export LEAN_PATH="$TASK_PATH"
cd "$TASK_ROOT"
"$TASK_LEAN" -o "${1%.lean}.olean" "$1"
