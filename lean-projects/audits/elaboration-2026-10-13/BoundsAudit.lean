import RiffleUpperV2.Completed
import RiffleLowerV2.Completed
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  for decl in [``RiffleUpperV2.Completed.firstMoment,
      ``RiffleUpperV2.Completed.conditionalEdges,
      ``RiffleUpperV2.Completed.empiricalUpper,
      ``RiffleUpperV2.Completed.profileUpper,
      ``RiffleUpperV2.Completed.criticalUpper,
      ``RiffleUpperV2.Completed.randomUpper,
      ``RiffleLowerV2.EmpiricalLower.empiricalCombined,
      ``RiffleLowerV2.MacroscopicLower.macroscopicIntegrable,
      ``RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto,
      ``RiffleLowerV2.ProfileTransfer.profileTransfer] do
    let axs ← Lean.collectAxioms decl
    logInfo m!"{decl}: {axs}"
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "Unaccepted dependency {a} in {decl}"
  logInfo "COMPLETED_BOUNDS_TRUST_OK"
