#!/bin/bash
set -euo pipefail
task_root="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
compiler="$task_root/.tooling/lean-4.19.0-darwin_aarch64"
mathlib="$task_root/.tooling/mathlib"
if [ "$#" -ne 1 ]; then
  echo 'Usage: check.sh Shuffle/Module.lean' >&2
  exit 2
fi
case "$1" in
  /*) source_file="$1" ;;
  *) source_file="$task_root/$1" ;;
esac
export PATH="$compiler/bin:$PATH"
cd "$mathlib"
exec "$compiler/bin/lake" env bash -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  exec lean --root="$1" -o "${2%.lean}.olean" "$2"
' _ "$task_root" "$source_file"
