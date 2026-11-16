#!/bin/sh
set -eu
TASK_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$TASK_ROOT"
TASK_LAKE="$TASK_ROOT/.tools/lean/bin/lake"
if [ ! -x "$TASK_LAKE" ]; then TASK_LAKE=$(command -v lake); fi
mkdir -p logs
"$TASK_LAKE" build > logs/build.log 2>&1
cat logs/build.log
"$TASK_LAKE" env lean -DwarningAsError=true Audit.lean > logs/axioms.log
"$TASK_LAKE" env lean -DwarningAsError=true Dependencies.lean > logs/dependencies.log
python3 scripts/verify.py
