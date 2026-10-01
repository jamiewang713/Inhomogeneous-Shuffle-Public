import RiffleLowerV2.ProfileTransfer.Main
import RiffleLowerV2.EmpiricalLower.Main
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true

example : RiffleLowerV2.Targets.JointPsiContinuity := RiffleLowerV2.ProfileTransfer.jointPsiContinuity
#print axioms RiffleLowerV2.ProfileTransfer.jointPsiContinuity
example : RiffleLowerV2.Targets.ProfileTransferTarget := RiffleLowerV2.ProfileTransfer.profileTransfer
#print axioms RiffleLowerV2.ProfileTransfer.profileTransfer
example : RiffleLowerV2.Targets.MarginTransferTarget := RiffleLowerV2.ProfileTransfer.marginTransfer
#print axioms RiffleLowerV2.ProfileTransfer.marginTransfer
example : RiffleLowerV2.Targets.GenericQuadrature := RiffleLowerV2.ProfileTransfer.genericQuadrature
#print axioms RiffleLowerV2.ProfileTransfer.genericQuadrature
example : RiffleLowerV2.Targets.EmpiricalCombinedTarget := RiffleLowerV2.EmpiricalLower.empiricalCombined
#print axioms RiffleLowerV2.EmpiricalLower.empiricalCombined
example : RiffleLowerV2.Targets.ColdOnlyTarget := RiffleLowerV2.EmpiricalLower.coldOnly
#print axioms RiffleLowerV2.EmpiricalLower.coldOnly
example : RiffleLowerV2.Targets.ManyEdgesTarget := RiffleLowerV2.EmpiricalLower.manyEdges
#print axioms RiffleLowerV2.EmpiricalLower.manyEdges
example : RiffleLowerV2.Targets.FiniteLargestWordTV := RiffleLowerV2.EmpiricalLower.finiteLargestWordTV
#print axioms RiffleLowerV2.EmpiricalLower.finiteLargestWordTV
example : RiffleLowerV2.Targets.LargestOnlyTarget := RiffleLowerV2.EmpiricalLower.largestOnly
#print axioms RiffleLowerV2.EmpiricalLower.largestOnly

#check RiffleLowerV2.ProfileTransfer.transferThreshold_spec
#print RiffleLowerV2.Targets.MacroscopicIntegrableTarget
#print RiffleLowerV2.ScalarIntegrable

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in [``RiffleLowerV2.ProfileTransfer.jointPsiContinuity, ``RiffleLowerV2.ProfileTransfer.profileTransfer, ``RiffleLowerV2.ProfileTransfer.marginTransfer, ``RiffleLowerV2.ProfileTransfer.genericQuadrature, ``RiffleLowerV2.EmpiricalLower.empiricalCombined, ``RiffleLowerV2.EmpiricalLower.coldOnly, ``RiffleLowerV2.EmpiricalLower.manyEdges, ``RiffleLowerV2.EmpiricalLower.finiteLargestWordTV, ``RiffleLowerV2.EmpiricalLower.largestOnly] do
    unless (env.find? name).any (fun info => info.isTheorem) do
      throwError "Required export is not a theorem: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom: {name}: {ax}"
  logInfo "LB11_NINE_INPUT_THEOREMS_VERIFIED"
