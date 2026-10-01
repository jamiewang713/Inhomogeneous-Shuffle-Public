import RiffleLowerV2.Completed
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true

example : RiffleLowerV2.Targets.ColumnIndependence := RiffleLowerV2.Model.columnIndependence
example : RiffleLowerV2.Targets.GraphRepresentation := RiffleLowerV2.Model.graphRepresentation
example : RiffleLowerV2.Targets.GraphEventIdentity := RiffleLowerV2.Model.graphEventIdentity
example : RiffleLowerV2.Targets.PhysicalMatrixBridge := RiffleLowerV2.Model.physicalMatrixBridge
example : RiffleLowerV2.Targets.InversionTV := RiffleLowerV2.Model.inversionTV
example : RiffleLowerV2.Targets.RowRelabeling := RiffleLowerV2.Model.rowRelabeling
example : RiffleLowerV2.Targets.StableTie := RiffleLowerV2.Model.stableTie
example : RiffleLowerV2.Targets.PrefixRanks := RiffleLowerV2.Model.prefixRanks
example : RiffleLowerV2.Targets.SuccessiveThinning := RiffleLowerV2.Thinning.successiveThinning
example : RiffleLowerV2.Targets.PrefixTails := RiffleLowerV2.Thinning.prefixTails
example : RiffleLowerV2.Targets.AllPrefixConcentration := RiffleLowerV2.Thinning.allPrefixConcentration
example : RiffleLowerV2.Targets.PrefixFailureUniform := RiffleLowerV2.Thinning.prefixFailureUniform
example : RiffleLowerV2.Targets.ResidualLaw := RiffleLowerV2.Thinning.residualLaw
example : RiffleLowerV2.Targets.HypergeometricTransform := RiffleLowerV2.Thinning.hypergeometricTransform
example : RiffleLowerV2.Targets.MaximalMeanIdentity := RiffleLowerV2.Thinning.maximalMeanIdentity
example : RiffleLowerV2.Targets.ExactJointFactorial := RiffleLowerV2.Factorial.exactJointFactorial
example : RiffleLowerV2.Targets.RelativeJointFactorial := RiffleLowerV2.Factorial.relativeJointFactorial
example : RiffleLowerV2.Targets.BonferroniSandwich := RiffleLowerV2.Factorial.bonferroniSandwich
example : RiffleLowerV2.Targets.BonferroniProduct := RiffleLowerV2.Factorial.bonferroniProduct
example : RiffleLowerV2.Targets.CentralComparison := RiffleLowerV2.Factorial.centralComparison
example : RiffleLowerV2.Targets.CentralComparisonOne := RiffleLowerV2.Factorial.centralComparisonOne
example : RiffleLowerV2.Targets.RareSandwich := RiffleLowerV2.Factorial.rareSandwich
example : RiffleLowerV2.Targets.ResidualJointFactorial := RiffleLowerV2.Factorial.residualJointFactorial
example : RiffleLowerV2.Targets.ResidualRelativeFactorial := RiffleLowerV2.Factorial.residualRelativeFactorial
example : RiffleLowerV2.Targets.ResidualMeanComparison := RiffleLowerV2.Factorial.residualMeanComparison
example : RiffleLowerV2.Targets.ComponentConcentration := RiffleLowerV2.Ascent.componentConcentration
example : RiffleLowerV2.Targets.ComponentExpectation := RiffleLowerV2.Ascent.componentExpectation
example : RiffleLowerV2.Targets.UniformScan := RiffleLowerV2.Ascent.uniformScan
example : RiffleLowerV2.Targets.ComponentComparison := RiffleLowerV2.Ascent.componentComparison
example : RiffleLowerV2.Targets.UniformGraphScan := RiffleLowerV2.Ascent.uniformGraphScan
example : RiffleLowerV2.Targets.RelativeOrderIndependence := RiffleLowerV2.Ascent.relativeOrderIndependence
example : RiffleLowerV2.Targets.BoundaryAscentProbability := RiffleLowerV2.Ascent.boundaryAscentProbability
example : RiffleLowerV2.Targets.BernoulliMGF := RiffleLowerV2.Ascent.bernoulliMGF
example : RiffleLowerV2.Targets.LeastSuccessfulTranslate := RiffleLowerV2.Ascent.leastSuccessfulTranslate
example : RiffleLowerV2.Targets.ComponentConcentrationTwoSided := RiffleLowerV2.Ascent.componentConcentrationTwoSided
example : RiffleLowerV2.Targets.ColdWitnessTarget := RiffleLowerV2.Witness.coldWitness
example : RiffleLowerV2.Targets.OneColumnTiltTarget := RiffleLowerV2.Witness.oneColumnTilt
example : RiffleLowerV2.Targets.EmpiricalTiltTarget := RiffleLowerV2.Witness.empiricalTilt
example : RiffleLowerV2.Targets.LB05Target := RiffleLowerV2.Witness.lB05
example : RiffleLowerV2.Targets.RoundedTypeTarget := RiffleLowerV2.Types.roundedType
example : RiffleLowerV2.Targets.MarginTransferTarget := RiffleLowerV2.ProfileTransfer.marginTransfer
example : RiffleLowerV2.Targets.ProfileTransferTarget := RiffleLowerV2.ProfileTransfer.profileTransfer
example : RiffleLowerV2.Targets.GenericQuadrature := RiffleLowerV2.ProfileTransfer.genericQuadrature
example : RiffleLowerV2.Targets.JointPsiContinuity := RiffleLowerV2.ProfileTransfer.jointPsiContinuity
example : RiffleLowerV2.Targets.UniformOccupancy := RiffleLowerV2.Occupancy.uniformOccupancy
example : RiffleLowerV2.Targets.ConditionalCollisionStability := RiffleLowerV2.Occupancy.conditionalCollisionStability
example : RiffleLowerV2.Targets.CollisionChebyshev := RiffleLowerV2.Occupancy.collisionChebyshev
example : RiffleLowerV2.Targets.LocalizationTarget := RiffleLowerV2.Localization.localization
example : RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget := RiffleLowerV2.Localization.coldGeometryFromEmpirical
example : RiffleLowerV2.Targets.RelativeEndpointTarget := RiffleLowerV2.Localization.relativeEndpoint
example : RiffleLowerV2.Targets.DeterministicColdGeometryTarget := RiffleLowerV2.Localization.deterministicColdGeometry
example : RiffleLowerV2.Targets.LB09Target := RiffleLowerV2.Localization.lB09
example : RiffleLowerV2.Targets.LargestOnlyTarget := RiffleLowerV2.EmpiricalLower.largestOnly
example : RiffleLowerV2.Targets.ColdOnlyTarget := RiffleLowerV2.EmpiricalLower.coldOnly
example : RiffleLowerV2.Targets.EmpiricalCombinedTarget := RiffleLowerV2.EmpiricalLower.empiricalCombined
example : RiffleLowerV2.Targets.FiniteLargestWordTV := RiffleLowerV2.EmpiricalLower.finiteLargestWordTV
example : RiffleLowerV2.Targets.ManyEdgesTarget := RiffleLowerV2.EmpiricalLower.manyEdges
example : RiffleLowerV2.Targets.MacroscopicIntegrableTarget := RiffleLowerV2.MacroscopicLower.macroscopicIntegrable

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleName in #[`RiffleLowerV2.Model.Main, `RiffleLowerV2.Thinning.Main, `RiffleLowerV2.Factorial.Main, `RiffleLowerV2.Ascent.Main, `RiffleLowerV2.Witness.Main, `RiffleLowerV2.Types.Main, `RiffleLowerV2.ProfileTransfer.Main, `RiffleLowerV2.Occupancy.Main, `RiffleLowerV2.Localization.Main, `RiffleLowerV2.EmpiricalLower.Main, `RiffleLowerV2.MacroscopicLower.Main] do
    unless env.header.moduleNames.contains moduleName do
      throwError "Completed umbrella missed lane entry point {moduleName}"
  for (name, target) in #[(`RiffleLowerV2.Model.columnIndependence, `RiffleLowerV2.Targets.ColumnIndependence), (`RiffleLowerV2.Model.graphRepresentation, `RiffleLowerV2.Targets.GraphRepresentation), (`RiffleLowerV2.Model.graphEventIdentity, `RiffleLowerV2.Targets.GraphEventIdentity), (`RiffleLowerV2.Model.physicalMatrixBridge, `RiffleLowerV2.Targets.PhysicalMatrixBridge), (`RiffleLowerV2.Model.inversionTV, `RiffleLowerV2.Targets.InversionTV), (`RiffleLowerV2.Model.rowRelabeling, `RiffleLowerV2.Targets.RowRelabeling), (`RiffleLowerV2.Model.stableTie, `RiffleLowerV2.Targets.StableTie), (`RiffleLowerV2.Model.prefixRanks, `RiffleLowerV2.Targets.PrefixRanks), (`RiffleLowerV2.Thinning.successiveThinning, `RiffleLowerV2.Targets.SuccessiveThinning), (`RiffleLowerV2.Thinning.prefixTails, `RiffleLowerV2.Targets.PrefixTails), (`RiffleLowerV2.Thinning.allPrefixConcentration, `RiffleLowerV2.Targets.AllPrefixConcentration), (`RiffleLowerV2.Thinning.prefixFailureUniform, `RiffleLowerV2.Targets.PrefixFailureUniform), (`RiffleLowerV2.Thinning.residualLaw, `RiffleLowerV2.Targets.ResidualLaw), (`RiffleLowerV2.Thinning.hypergeometricTransform, `RiffleLowerV2.Targets.HypergeometricTransform), (`RiffleLowerV2.Thinning.maximalMeanIdentity, `RiffleLowerV2.Targets.MaximalMeanIdentity), (`RiffleLowerV2.Factorial.exactJointFactorial, `RiffleLowerV2.Targets.ExactJointFactorial), (`RiffleLowerV2.Factorial.relativeJointFactorial, `RiffleLowerV2.Targets.RelativeJointFactorial), (`RiffleLowerV2.Factorial.bonferroniSandwich, `RiffleLowerV2.Targets.BonferroniSandwich), (`RiffleLowerV2.Factorial.bonferroniProduct, `RiffleLowerV2.Targets.BonferroniProduct), (`RiffleLowerV2.Factorial.centralComparison, `RiffleLowerV2.Targets.CentralComparison), (`RiffleLowerV2.Factorial.centralComparisonOne, `RiffleLowerV2.Targets.CentralComparisonOne), (`RiffleLowerV2.Factorial.rareSandwich, `RiffleLowerV2.Targets.RareSandwich), (`RiffleLowerV2.Factorial.residualJointFactorial, `RiffleLowerV2.Targets.ResidualJointFactorial), (`RiffleLowerV2.Factorial.residualRelativeFactorial, `RiffleLowerV2.Targets.ResidualRelativeFactorial), (`RiffleLowerV2.Factorial.residualMeanComparison, `RiffleLowerV2.Targets.ResidualMeanComparison), (`RiffleLowerV2.Ascent.componentConcentration, `RiffleLowerV2.Targets.ComponentConcentration), (`RiffleLowerV2.Ascent.componentExpectation, `RiffleLowerV2.Targets.ComponentExpectation), (`RiffleLowerV2.Ascent.uniformScan, `RiffleLowerV2.Targets.UniformScan), (`RiffleLowerV2.Ascent.componentComparison, `RiffleLowerV2.Targets.ComponentComparison), (`RiffleLowerV2.Ascent.uniformGraphScan, `RiffleLowerV2.Targets.UniformGraphScan), (`RiffleLowerV2.Ascent.relativeOrderIndependence, `RiffleLowerV2.Targets.RelativeOrderIndependence), (`RiffleLowerV2.Ascent.boundaryAscentProbability, `RiffleLowerV2.Targets.BoundaryAscentProbability), (`RiffleLowerV2.Ascent.bernoulliMGF, `RiffleLowerV2.Targets.BernoulliMGF), (`RiffleLowerV2.Ascent.leastSuccessfulTranslate, `RiffleLowerV2.Targets.LeastSuccessfulTranslate), (`RiffleLowerV2.Ascent.componentConcentrationTwoSided, `RiffleLowerV2.Targets.ComponentConcentrationTwoSided), (`RiffleLowerV2.Witness.coldWitness, `RiffleLowerV2.Targets.ColdWitnessTarget), (`RiffleLowerV2.Witness.oneColumnTilt, `RiffleLowerV2.Targets.OneColumnTiltTarget), (`RiffleLowerV2.Witness.empiricalTilt, `RiffleLowerV2.Targets.EmpiricalTiltTarget), (`RiffleLowerV2.Witness.lB05, `RiffleLowerV2.Targets.LB05Target), (`RiffleLowerV2.Types.roundedType, `RiffleLowerV2.Targets.RoundedTypeTarget), (`RiffleLowerV2.ProfileTransfer.marginTransfer, `RiffleLowerV2.Targets.MarginTransferTarget), (`RiffleLowerV2.ProfileTransfer.profileTransfer, `RiffleLowerV2.Targets.ProfileTransferTarget), (`RiffleLowerV2.ProfileTransfer.genericQuadrature, `RiffleLowerV2.Targets.GenericQuadrature), (`RiffleLowerV2.ProfileTransfer.jointPsiContinuity, `RiffleLowerV2.Targets.JointPsiContinuity), (`RiffleLowerV2.Occupancy.uniformOccupancy, `RiffleLowerV2.Targets.UniformOccupancy), (`RiffleLowerV2.Occupancy.conditionalCollisionStability, `RiffleLowerV2.Targets.ConditionalCollisionStability), (`RiffleLowerV2.Occupancy.collisionChebyshev, `RiffleLowerV2.Targets.CollisionChebyshev), (`RiffleLowerV2.Localization.localization, `RiffleLowerV2.Targets.LocalizationTarget), (`RiffleLowerV2.Localization.coldGeometryFromEmpirical, `RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget), (`RiffleLowerV2.Localization.relativeEndpoint, `RiffleLowerV2.Targets.RelativeEndpointTarget), (`RiffleLowerV2.Localization.deterministicColdGeometry, `RiffleLowerV2.Targets.DeterministicColdGeometryTarget), (`RiffleLowerV2.Localization.lB09, `RiffleLowerV2.Targets.LB09Target), (`RiffleLowerV2.EmpiricalLower.largestOnly, `RiffleLowerV2.Targets.LargestOnlyTarget), (`RiffleLowerV2.EmpiricalLower.coldOnly, `RiffleLowerV2.Targets.ColdOnlyTarget), (`RiffleLowerV2.EmpiricalLower.empiricalCombined, `RiffleLowerV2.Targets.EmpiricalCombinedTarget), (`RiffleLowerV2.EmpiricalLower.finiteLargestWordTV, `RiffleLowerV2.Targets.FiniteLargestWordTV), (`RiffleLowerV2.EmpiricalLower.manyEdges, `RiffleLowerV2.Targets.ManyEdgesTarget), (`RiffleLowerV2.MacroscopicLower.macroscopicIntegrable, `RiffleLowerV2.Targets.MacroscopicIntegrableTarget)] do
    let some ci := env.find? name | throwError "Missing umbrella export {name}"
    unless ci.isTheorem && ci.type.isConstOf target do
      throwError "Wrong umbrella export type {name}"
    for ax in (← Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected umbrella axiom {ax}"
  logInfo "COMPLETED_UMBRELLA_ONLY_58_THEOREMS_VERIFIED"
