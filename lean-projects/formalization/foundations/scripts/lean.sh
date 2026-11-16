#!/bin/sh
set -eu
TASK_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$TASK_ROOT"
TASK_LEAN="$TASK_ROOT/.tools/lean/bin/lean"
if [ ! -x "$TASK_LEAN" ]; then TASK_LEAN=$(command -v lean); fi
TASK_PATH="$TASK_ROOT/.lake/build/lib/lean"
for TASK_PKG in "$TASK_ROOT"/.lake/packages/*; do
  TASK_PATH="$TASK_PATH:$TASK_PKG/.lake/build/lib/lean"
done
export LEAN_PATH="$TASK_PATH"
exec "$TASK_LEAN" "$@"
