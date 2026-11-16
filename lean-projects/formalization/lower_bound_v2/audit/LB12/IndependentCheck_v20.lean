import Contracts
import Contracts.v1
import Contracts.v1.AdditionalFinite
import Contracts.v1.Ascent
import Contracts.v1.AssemblyInputs
import Contracts.v1.Endpoints
import Contracts.v1.FactorialOccupancy
import Contracts.v1.ModelThinning
import Contracts.v1.TransferFinite
import Contracts.v1.WitnessGeometry
import RiffleLowerV2
import RiffleLowerV2.Ascent.Asymptotic
import RiffleLowerV2.Ascent.Components
import RiffleLowerV2.Ascent.Components.Charging
import RiffleLowerV2.Ascent.Components.Clipping
import RiffleLowerV2.Ascent.Concentration
import RiffleLowerV2.Ascent.Expectation
import RiffleLowerV2.Ascent.FiniteConsequences
import RiffleLowerV2.Ascent.FiniteProbability
import RiffleLowerV2.Ascent.MGF
import RiffleLowerV2.Ascent.Main
import RiffleLowerV2.Ascent.Mixture
import RiffleLowerV2.Ascent.Quantitative
import RiffleLowerV2.Ascent.RelativeOrder
import RiffleLowerV2.Ascent.RelativeOrder.Basic
import RiffleLowerV2.Ascent.RelativeOrder.Boundary
import RiffleLowerV2.Ascent.RelativeOrder.Check
import RiffleLowerV2.Ascent.RelativeOrder.Law
import RiffleLowerV2.Ascent.RelativeOrder.Weighted
import RiffleLowerV2.Ascent.Selection
import RiffleLowerV2.Ascent.Test
import RiffleLowerV2.Ascent.UniformBaseline
import RiffleLowerV2.Completed
import RiffleLowerV2.EmpiricalLower.Cold
import RiffleLowerV2.EmpiricalLower.CollisionMean
import RiffleLowerV2.EmpiricalLower.LargestAsymptotic
import RiffleLowerV2.EmpiricalLower.LargestAsymptotic.Numerical
import RiffleLowerV2.EmpiricalLower.LargestFinite
import RiffleLowerV2.EmpiricalLower.Main
import RiffleLowerV2.EmpiricalLower.ManyEdges
import RiffleLowerV2.EmpiricalLower.Scan
import RiffleLowerV2.Factorial.Basic
import RiffleLowerV2.Factorial.Bonferroni
import RiffleLowerV2.Factorial.Central
import RiffleLowerV2.Factorial.Exact
import RiffleLowerV2.Factorial.Main
import RiffleLowerV2.Factorial.MomentScales
import RiffleLowerV2.Factorial.PoissonPolynomial
import RiffleLowerV2.Factorial.PolynomialMoments
import RiffleLowerV2.Factorial.Ratios
import RiffleLowerV2.Factorial.Relative
import RiffleLowerV2.Factorial.RelativeFromExact
import RiffleLowerV2.Factorial.RelativeTargets
import RiffleLowerV2.Factorial.Requests
import RiffleLowerV2.Factorial.Residual
import RiffleLowerV2.Factorial.ResidualEstimates
import RiffleLowerV2.Localization.Bridge
import RiffleLowerV2.Localization.ColdSet
import RiffleLowerV2.Localization.Concentration
import RiffleLowerV2.Localization.Edges
import RiffleLowerV2.Localization.Endpoints
import RiffleLowerV2.Localization.Endpoints.Check
import RiffleLowerV2.Localization.Endpoints.Coordinates
import RiffleLowerV2.Localization.Endpoints.Counts
import RiffleLowerV2.Localization.Endpoints.Error
import RiffleLowerV2.Localization.Endpoints.Means
import RiffleLowerV2.Localization.Endpoints.Partitions
import RiffleLowerV2.Localization.Endpoints.ProductWeights
import RiffleLowerV2.Localization.EventBounds
import RiffleLowerV2.Localization.Events
import RiffleLowerV2.Localization.Geometry
import RiffleLowerV2.Localization.Geometry.Algebra
import RiffleLowerV2.Localization.Geometry.Bounds
import RiffleLowerV2.Localization.Geometry.Check
import RiffleLowerV2.Localization.Geometry.Consequences
import RiffleLowerV2.Localization.Geometry.Empirical
import RiffleLowerV2.Localization.Geometry.Rates
import RiffleLowerV2.Localization.Intervals
import RiffleLowerV2.Localization.Main
import RiffleLowerV2.Localization.Probability
import RiffleLowerV2.Localization.ProbabilityIntervals
import RiffleLowerV2.Localization.RankBarriers
import RiffleLowerV2.Localization.WordOrder
import RiffleLowerV2.Localization.Words
import RiffleLowerV2.MacroscopicLower.Main
import RiffleLowerV2.MacroscopicLower.Parameters
import RiffleLowerV2.Model.ComponentFibers
import RiffleLowerV2.Model.FiberCounts
import RiffleLowerV2.Model.FiniteLaws
import RiffleLowerV2.Model.GraphLaw
import RiffleLowerV2.Model.GraphSorting
import RiffleLowerV2.Model.Main
import RiffleLowerV2.Model.Physical
import RiffleLowerV2.Model.Sorting
import RiffleLowerV2.Occupancy.CentralModel
import RiffleLowerV2.Occupancy.CentralScales
import RiffleLowerV2.Occupancy.Check
import RiffleLowerV2.Occupancy.Conditional
import RiffleLowerV2.Occupancy.ConditionalInputs
import RiffleLowerV2.Occupancy.Covariance
import RiffleLowerV2.Occupancy.FiniteProbability
import RiffleLowerV2.Occupancy.Forcing
import RiffleLowerV2.Occupancy.Main
import RiffleLowerV2.Occupancy.Marginal
import RiffleLowerV2.Occupancy.MarginalNumerical
import RiffleLowerV2.Occupancy.ModelInputs
import RiffleLowerV2.Occupancy.Nonrare
import RiffleLowerV2.Occupancy.Numerical
import RiffleLowerV2.Occupancy.Poisson
import RiffleLowerV2.Occupancy.RarePair
import RiffleLowerV2.Occupancy.RegimeAlgebra
import RiffleLowerV2.Occupancy.Scales
import RiffleLowerV2.ProfileTransfer.Compat.Error
import RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature
import RiffleLowerV2.ProfileTransfer.Compat.IntegralEnvelope
import RiffleLowerV2.ProfileTransfer.Compat.LatticeCounts
import RiffleLowerV2.ProfileTransfer.Empirical
import RiffleLowerV2.ProfileTransfer.Endpoint
import RiffleLowerV2.ProfileTransfer.Extrema
import RiffleLowerV2.ProfileTransfer.Main
import RiffleLowerV2.ProfileTransfer.Margin
import RiffleLowerV2.ProfileTransfer.Parameters
import RiffleLowerV2.ProfileTransfer.Quadrature
import RiffleLowerV2.ProfileTransfer.Spatial
import RiffleLowerV2.Shared
import RiffleLowerV2.Shared.Adapters
import RiffleLowerV2.Shared.Empirical
import RiffleLowerV2.Shared.Geometry
import RiffleLowerV2.Shared.Model
import RiffleLowerV2.Shared.Path
import RiffleLowerV2.Shared.Smoke
import RiffleLowerV2.Shared.Statistics
import RiffleLowerV2.Thinning.AllPrefixes
import RiffleLowerV2.Thinning.Check
import RiffleLowerV2.Thinning.ColumnSampling
import RiffleLowerV2.Thinning.Compat.Check
import RiffleLowerV2.Thinning.Compat.Conditioning
import RiffleLowerV2.Thinning.Compat.FiniteLaw
import RiffleLowerV2.Thinning.Compat.Hypergeometric
import RiffleLowerV2.Thinning.Compat.HypergeometricConcentration
import RiffleLowerV2.Thinning.Compat.HypergeometricMoments
import RiffleLowerV2.Thinning.Compat.ResidualSampling
import RiffleLowerV2.Thinning.Compat.SamplingCheck
import RiffleLowerV2.Thinning.Compat.SubsetSampling
import RiffleLowerV2.Thinning.Compat.SubsetTransform
import RiffleLowerV2.Thinning.Main
import RiffleLowerV2.Thinning.MaximalWord
import RiffleLowerV2.Thinning.PMFTools
import RiffleLowerV2.Thinning.PrefixCoordinates
import RiffleLowerV2.Thinning.Prefixes
import RiffleLowerV2.Thinning.Process
import RiffleLowerV2.Thinning.Recursion
import RiffleLowerV2.Thinning.Residual
import RiffleLowerV2.Thinning.Residual.Check
import RiffleLowerV2.Thinning.Residual.Independence
import RiffleLowerV2.Thinning.Residual.IndependenceCheck
import RiffleLowerV2.Thinning.Residual.Prefix
import RiffleLowerV2.Thinning.Residual.PrefixCheck
import RiffleLowerV2.Thinning.Sampling
import RiffleLowerV2.Thinning.Tails
import RiffleLowerV2.Thinning.UniformError
import RiffleLowerV2.Types.Approximation
import RiffleLowerV2.Types.ClassEntropy
import RiffleLowerV2.Types.Construction
import RiffleLowerV2.Types.Counting
import RiffleLowerV2.Types.Empty
import RiffleLowerV2.Types.EntropyBounds
import RiffleLowerV2.Types.Main
import RiffleLowerV2.Types.MassBins
import RiffleLowerV2.Types.Partition
import RiffleLowerV2.Types.Rates
import RiffleLowerV2.Types.Rounding
import RiffleLowerV2.Types.Truncation
import RiffleLowerV2.Types.WordEstimates
import RiffleLowerV2.Witness.Continuous
import RiffleLowerV2.Witness.Empirical
import RiffleLowerV2.Witness.EmpiricalTilt
import RiffleLowerV2.Witness.Finite
import RiffleLowerV2.Witness.Main
import RiffleLowerV2.Witness.OneColumn
import RiffleLowerV2.Witness.OneColumnBasic
import RiffleLowerV2.Witness.Rounding
import RiffleLowerV2.Witness.Selection

import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
set_option pp.funBinderTypes true
set_option pp.universes false

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let required := #[(`RiffleLowerV2.Model.columnIndependence, `RiffleLowerV2.Targets.ColumnIndependence),
(`RiffleLowerV2.Model.graphRepresentation, `RiffleLowerV2.Targets.GraphRepresentation),
(`RiffleLowerV2.Model.graphEventIdentity, `RiffleLowerV2.Targets.GraphEventIdentity),
(`RiffleLowerV2.Model.physicalMatrixBridge, `RiffleLowerV2.Targets.PhysicalMatrixBridge),
(`RiffleLowerV2.Model.inversionTV, `RiffleLowerV2.Targets.InversionTV),
(`RiffleLowerV2.Model.rowRelabeling, `RiffleLowerV2.Targets.RowRelabeling),
(`RiffleLowerV2.Model.stableTie, `RiffleLowerV2.Targets.StableTie),
(`RiffleLowerV2.Model.prefixRanks, `RiffleLowerV2.Targets.PrefixRanks),
(`RiffleLowerV2.Thinning.successiveThinning, `RiffleLowerV2.Targets.SuccessiveThinning),
(`RiffleLowerV2.Thinning.prefixTails, `RiffleLowerV2.Targets.PrefixTails),
(`RiffleLowerV2.Thinning.allPrefixConcentration, `RiffleLowerV2.Targets.AllPrefixConcentration),
(`RiffleLowerV2.Thinning.prefixFailureUniform, `RiffleLowerV2.Targets.PrefixFailureUniform),
(`RiffleLowerV2.Thinning.residualLaw, `RiffleLowerV2.Targets.ResidualLaw),
(`RiffleLowerV2.Thinning.hypergeometricTransform, `RiffleLowerV2.Targets.HypergeometricTransform),
(`RiffleLowerV2.Thinning.maximalMeanIdentity, `RiffleLowerV2.Targets.MaximalMeanIdentity),
(`RiffleLowerV2.Factorial.exactJointFactorial, `RiffleLowerV2.Targets.ExactJointFactorial),
(`RiffleLowerV2.Factorial.relativeJointFactorial, `RiffleLowerV2.Targets.RelativeJointFactorial),
(`RiffleLowerV2.Factorial.bonferroniSandwich, `RiffleLowerV2.Targets.BonferroniSandwich),
(`RiffleLowerV2.Factorial.bonferroniProduct, `RiffleLowerV2.Targets.BonferroniProduct),
(`RiffleLowerV2.Factorial.centralComparison, `RiffleLowerV2.Targets.CentralComparison),
(`RiffleLowerV2.Factorial.centralComparisonOne, `RiffleLowerV2.Targets.CentralComparisonOne),
(`RiffleLowerV2.Factorial.rareSandwich, `RiffleLowerV2.Targets.RareSandwich),
(`RiffleLowerV2.Factorial.residualJointFactorial, `RiffleLowerV2.Targets.ResidualJointFactorial),
(`RiffleLowerV2.Factorial.residualRelativeFactorial, `RiffleLowerV2.Targets.ResidualRelativeFactorial),
(`RiffleLowerV2.Factorial.residualMeanComparison, `RiffleLowerV2.Targets.ResidualMeanComparison),
(`RiffleLowerV2.Ascent.componentConcentration, `RiffleLowerV2.Targets.ComponentConcentration),
(`RiffleLowerV2.Ascent.componentExpectation, `RiffleLowerV2.Targets.ComponentExpectation),
(`RiffleLowerV2.Ascent.uniformScan, `RiffleLowerV2.Targets.UniformScan),
(`RiffleLowerV2.Ascent.componentComparison, `RiffleLowerV2.Targets.ComponentComparison),
(`RiffleLowerV2.Ascent.uniformGraphScan, `RiffleLowerV2.Targets.UniformGraphScan),
(`RiffleLowerV2.Ascent.relativeOrderIndependence, `RiffleLowerV2.Targets.RelativeOrderIndependence),
(`RiffleLowerV2.Ascent.boundaryAscentProbability, `RiffleLowerV2.Targets.BoundaryAscentProbability),
(`RiffleLowerV2.Ascent.bernoulliMGF, `RiffleLowerV2.Targets.BernoulliMGF),
(`RiffleLowerV2.Ascent.leastSuccessfulTranslate, `RiffleLowerV2.Targets.LeastSuccessfulTranslate),
(`RiffleLowerV2.Ascent.componentConcentrationTwoSided, `RiffleLowerV2.Targets.ComponentConcentrationTwoSided),
(`RiffleLowerV2.Witness.coldWitness, `RiffleLowerV2.Targets.ColdWitnessTarget),
(`RiffleLowerV2.Witness.oneColumnTilt, `RiffleLowerV2.Targets.OneColumnTiltTarget),
(`RiffleLowerV2.Witness.empiricalTilt, `RiffleLowerV2.Targets.EmpiricalTiltTarget),
(`RiffleLowerV2.Witness.lB05, `RiffleLowerV2.Targets.LB05Target),
(`RiffleLowerV2.Types.roundedType, `RiffleLowerV2.Targets.RoundedTypeTarget),
(`RiffleLowerV2.ProfileTransfer.marginTransfer, `RiffleLowerV2.Targets.MarginTransferTarget),
(`RiffleLowerV2.ProfileTransfer.profileTransfer, `RiffleLowerV2.Targets.ProfileTransferTarget),
(`RiffleLowerV2.ProfileTransfer.genericQuadrature, `RiffleLowerV2.Targets.GenericQuadrature),
(`RiffleLowerV2.ProfileTransfer.jointPsiContinuity, `RiffleLowerV2.Targets.JointPsiContinuity),
(`RiffleLowerV2.Occupancy.uniformOccupancy, `RiffleLowerV2.Targets.UniformOccupancy),
(`RiffleLowerV2.Occupancy.conditionalCollisionStability, `RiffleLowerV2.Targets.ConditionalCollisionStability),
(`RiffleLowerV2.Occupancy.collisionChebyshev, `RiffleLowerV2.Targets.CollisionChebyshev),
(`RiffleLowerV2.Localization.localization, `RiffleLowerV2.Targets.LocalizationTarget),
(`RiffleLowerV2.Localization.coldGeometryFromEmpirical, `RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget),
(`RiffleLowerV2.Localization.relativeEndpoint, `RiffleLowerV2.Targets.RelativeEndpointTarget),
(`RiffleLowerV2.Localization.deterministicColdGeometry, `RiffleLowerV2.Targets.DeterministicColdGeometryTarget),
(`RiffleLowerV2.Localization.lB09, `RiffleLowerV2.Targets.LB09Target),
(`RiffleLowerV2.EmpiricalLower.largestOnly, `RiffleLowerV2.Targets.LargestOnlyTarget),
(`RiffleLowerV2.EmpiricalLower.coldOnly, `RiffleLowerV2.Targets.ColdOnlyTarget),
(`RiffleLowerV2.EmpiricalLower.empiricalCombined, `RiffleLowerV2.Targets.EmpiricalCombinedTarget),
(`RiffleLowerV2.EmpiricalLower.finiteLargestWordTV, `RiffleLowerV2.Targets.FiniteLargestWordTV),
(`RiffleLowerV2.EmpiricalLower.manyEdges, `RiffleLowerV2.Targets.ManyEdgesTarget),
(`RiffleLowerV2.MacroscopicLower.macroscopicIntegrable, `RiffleLowerV2.Targets.MacroscopicIntegrableTarget)]
  for (name, target) in required do
    let some ci := env.find? name | throwError "Missing frozen export {name}"
    unless ci.isTheorem && ci.type.isConstOf target do
      throwError "Frozen export is not a theorem of its exact target: {name}"
    logInfo m!"EXACT_EXPORT_JSON {(Json.mkObj [("name", toJson name.toString), ("target", toJson target.toString)]).compress}"
  for (name, ci) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.allImportedModuleNames[idx]!.toString
      | none => ""
    if moduleName.startsWith "RiffleLowerV2" || moduleName.startsWith "Contracts" ||
        moduleName.startsWith "RiffleTimeProfile" || moduleName.startsWith "RiffleShuffle" then
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Illicit axiom dependency {ax} of {name}"
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .opaqueInfo _ => "opaque"
        | _ => "generated"
      if kind == "axiom" then throwError "Project axiom {name}"
      let ty ← liftTermElabM <| Meta.ppExpr ci.type
      let deps := (ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
      let val ← match ci.value? (allowOpaque := true) with
        | some v => do
            if ci.type.isSort then
              let doc ← liftTermElabM <| Meta.ppExpr v
              pure doc.pretty
            else pure ""
        | none => pure ""
      let row := Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName),
        ("kind", toJson kind), ("type", toJson ty.pretty), ("value", toJson val),
        ("type_dependencies", toJson (ci.type.getUsedConstants.map Name.toString)),
        ("value_dependencies", toJson (deps.map Name.toString)),
        ("all_direct_dependencies", toJson (ci.getUsedConstantsAsSet.toArray.map Name.toString)),
        ("axioms", toJson (axs.map Name.toString))]
      logInfo m!"DECLARATION_JSON {row.compress}"
  for root in #[`RiffleLowerV2.EmpiricalLower.empiricalCombined,
      `RiffleLowerV2.EmpiricalLower.coldOnly,
      `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable,
      `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto] do
    let mut queue := #[root]
    let mut seen : NameSet := {}
    let mut allNames : Array String := #[]
    let mut axioms : Array String := #[]
    let mut project : Array String := #[]
    while !queue.isEmpty do
      let name := queue.back!
      queue := queue.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some ci := env.find? name | throwError "Absent transitive dependency {name}"
      queue := queue ++ ci.getUsedConstantsAsSet.toArray
      allNames := allNames.push name.toString
      match ci with
      | .axiomInfo _ =>
        unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
          throwError "Forbidden axiom {name} in endpoint closure {root}"
        axioms := axioms.push name.toString
      | _ => pure ()
      let modName := match env.getModuleIdxFor? name with
        | some idx => env.allImportedModuleNames[idx]!.toString
        | none => ""
      if modName.startsWith "RiffleLowerV2" || modName.startsWith "Contracts" ||
          modName.startsWith "RiffleTimeProfile" || modName.startsWith "RiffleShuffle" then
        project := project.push name.toString
    let axs ← Lean.collectAxioms root
    logInfo m!"CLOSURE_JSON {(Json.mkObj [("root", toJson root.toString), ("reachable_count", toJson allNames.size), ("all_reachable_names", toJson allNames), ("project_reachable_names", toJson project), ("recursive_axioms", toJson axioms), ("collect_axioms", toJson (axs.map Name.toString))]).compress}"
  logInfo m!"MODULES_JSON {(toJson (env.allImportedModuleNames.map Name.toString)).compress}"


example {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) :
    RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts) (RiffleLowerV2.uniformPermutation N) =
    RiffleLowerV2.tv (RiffleLowerV2.physicalForwardLaw cuts) (RiffleLowerV2.uniformPermutation N) := by
  rw [RiffleLowerV2.physicalInverseLaw_eq_map]
  exact RiffleLowerV2.Model.inversionTV N _

#print RiffleLowerV2.EmpiricalLower.empiricalCombined
#print RiffleLowerV2.MacroscopicLower.macroscopicIntegrable
#print RiffleLowerV2.Targets.EmpiricalCombinedTarget
#print RiffleLowerV2.Targets.MacroscopicIntegrableTarget
#print RiffleLowerV2.ScalarIntegrable
#print RiffleLowerV2.ColdWitnessData
#print RiffleLowerV2.RoundedTypeData
#print RiffleLowerV2.ColdGeometryData
#print RiffleLowerV2.WitnessSpec
#print RiffleLowerV2.GeometrySpec
#print RiffleLowerV2.TypeDataSpec

open Lean Elab Command in
run_cmd logInfo "LB12_INDEPENDENT_AUDIT_PASSED"
