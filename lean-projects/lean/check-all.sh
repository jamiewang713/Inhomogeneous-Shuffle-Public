#!/bin/bash
set -euo pipefail
task_root="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
python3 "$task_root/audit/verify_contract.py"
python3 "$task_root/audit/index_declarations.py"
modules=(
  FiniteLaw FiniteLawExtras Conditioning Hypergeometric HypergeometricMoments
  HypergeometricBoundary HypergeometricConcentration HypergeometricAntiConcentration
  SubsetSampling ResidualSampling FixedColumns FiniteMixture RandomColumns
  ConditionalHypergeometric NonExhaustion AmbientCounterexample AmbientMatrixCounterexample
)
for module in "${modules[@]}"; do
  "$task_root/check.sh" "Shuffle/$module.lean"
  echo "Checked Shuffle.$module"
done
"$task_root/check.sh" Shuffle.lean
"$task_root/check.sh" audit/PrintAxioms.lean > "$task_root/audit/axiom-report.txt"
python3 "$task_root/audit/verify_axioms.py"
"$task_root/check.sh" audit/ExportDependencies.lean > "$task_root/audit/lean-dependencies.json"
python3 "$task_root/audit/verify_contract.py"
