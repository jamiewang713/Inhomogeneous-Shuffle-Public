import Contracts.v1.AdditionalFinite
import Contracts.v1.Ascent
import Contracts.v1.AssemblyInputs
import Contracts.v1.Endpoints
import Contracts.v1.FactorialOccupancy
import Contracts.v1.ModelThinning
import Contracts.v1.TransferFinite
import Contracts.v1.WitnessGeometry
import Contracts.v1
import Contracts
import RiffleLowerV2.Ascent.Asymptotic
import RiffleLowerV2.Ascent.Components.Charging
import RiffleLowerV2.Ascent.Components.Clipping
import RiffleLowerV2.Ascent.Components
import RiffleLowerV2.Ascent.Concentration
import RiffleLowerV2.Ascent.Expectation
import RiffleLowerV2.Ascent.FiniteConsequences
import RiffleLowerV2.Ascent.FiniteProbability
import RiffleLowerV2.Ascent.MGF
import RiffleLowerV2.Ascent.Main
import RiffleLowerV2.Ascent.Mixture
import RiffleLowerV2.Ascent.Quantitative
import RiffleLowerV2.Ascent.RelativeOrder.Basic
import RiffleLowerV2.Ascent.RelativeOrder.Boundary
import RiffleLowerV2.Ascent.RelativeOrder.Check
import RiffleLowerV2.Ascent.RelativeOrder.Law
import RiffleLowerV2.Ascent.RelativeOrder.Weighted
import RiffleLowerV2.Ascent.RelativeOrder
import RiffleLowerV2.Ascent.Selection
import RiffleLowerV2.Ascent.Test
import RiffleLowerV2.Ascent.UniformBaseline
import RiffleLowerV2.Completed
import RiffleLowerV2.EmpiricalLower.Cold
import RiffleLowerV2.EmpiricalLower.CollisionMean
import RiffleLowerV2.EmpiricalLower.LargestAsymptotic.Numerical
import RiffleLowerV2.EmpiricalLower.LargestAsymptotic
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
import RiffleLowerV2.Localization.Endpoints.Check
import RiffleLowerV2.Localization.Endpoints.Coordinates
import RiffleLowerV2.Localization.Endpoints.Counts
import RiffleLowerV2.Localization.Endpoints.Error
import RiffleLowerV2.Localization.Endpoints.Means
import RiffleLowerV2.Localization.Endpoints.Partitions
import RiffleLowerV2.Localization.Endpoints.ProductWeights
import RiffleLowerV2.Localization.Endpoints
import RiffleLowerV2.Localization.EventBounds
import RiffleLowerV2.Localization.Events
import RiffleLowerV2.Localization.Geometry.Algebra
import RiffleLowerV2.Localization.Geometry.Bounds
import RiffleLowerV2.Localization.Geometry.Check
import RiffleLowerV2.Localization.Geometry.Consequences
import RiffleLowerV2.Localization.Geometry.Empirical
import RiffleLowerV2.Localization.Geometry.Rates
import RiffleLowerV2.Localization.Geometry
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
import RiffleLowerV2.Shared.Adapters
import RiffleLowerV2.Shared.Empirical
import RiffleLowerV2.Shared.Geometry
import RiffleLowerV2.Shared.Model
import RiffleLowerV2.Shared.Path
import RiffleLowerV2.Shared.Smoke
import RiffleLowerV2.Shared.Statistics
import RiffleLowerV2.Shared
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
import RiffleLowerV2.Thinning.Residual.Check
import RiffleLowerV2.Thinning.Residual.Independence
import RiffleLowerV2.Thinning.Residual.IndependenceCheck
import RiffleLowerV2.Thinning.Residual.Prefix
import RiffleLowerV2.Thinning.Residual.PrefixCheck
import RiffleLowerV2.Thinning.Residual
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
import RiffleLowerV2
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true
set_option maxHeartbeats 0

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
  for (name, target) in #[(`RiffleLowerV2.Model.columnIndependence, `RiffleLowerV2.Targets.ColumnIndependence),
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
    (`RiffleLowerV2.MacroscopicLower.macroscopicIntegrable, `RiffleLowerV2.Targets.MacroscopicIntegrableTarget)] do
    let some ci := env.find? name | throwError "Missing required theorem {name}"
    unless ci.isTheorem && ci.type.isConstOf target do
      throwError "Wrong theorem kind or exact frozen type: {name}"
  let requiredModules : Array String := #["Contracts.v1.AdditionalFinite", "Contracts.v1.Ascent", "Contracts.v1.AssemblyInputs", "Contracts.v1.Endpoints", "Contracts.v1.FactorialOccupancy", "Contracts.v1.ModelThinning", "Contracts.v1.TransferFinite", "Contracts.v1.WitnessGeometry", "Contracts.v1", "Contracts", "RiffleLowerV2.Ascent.Asymptotic", "RiffleLowerV2.Ascent.Components.Charging", "RiffleLowerV2.Ascent.Components.Clipping", "RiffleLowerV2.Ascent.Components", "RiffleLowerV2.Ascent.Concentration", "RiffleLowerV2.Ascent.Expectation", "RiffleLowerV2.Ascent.FiniteConsequences", "RiffleLowerV2.Ascent.FiniteProbability", "RiffleLowerV2.Ascent.MGF", "RiffleLowerV2.Ascent.Main", "RiffleLowerV2.Ascent.Mixture", "RiffleLowerV2.Ascent.Quantitative", "RiffleLowerV2.Ascent.RelativeOrder.Basic", "RiffleLowerV2.Ascent.RelativeOrder.Boundary", "RiffleLowerV2.Ascent.RelativeOrder.Check", "RiffleLowerV2.Ascent.RelativeOrder.Law", "RiffleLowerV2.Ascent.RelativeOrder.Weighted", "RiffleLowerV2.Ascent.RelativeOrder", "RiffleLowerV2.Ascent.Selection", "RiffleLowerV2.Ascent.Test", "RiffleLowerV2.Ascent.UniformBaseline", "RiffleLowerV2.Completed", "RiffleLowerV2.EmpiricalLower.Cold", "RiffleLowerV2.EmpiricalLower.CollisionMean", "RiffleLowerV2.EmpiricalLower.LargestAsymptotic.Numerical", "RiffleLowerV2.EmpiricalLower.LargestAsymptotic", "RiffleLowerV2.EmpiricalLower.LargestFinite", "RiffleLowerV2.EmpiricalLower.Main", "RiffleLowerV2.EmpiricalLower.ManyEdges", "RiffleLowerV2.EmpiricalLower.Scan", "RiffleLowerV2.Factorial.Basic", "RiffleLowerV2.Factorial.Bonferroni", "RiffleLowerV2.Factorial.Central", "RiffleLowerV2.Factorial.Exact", "RiffleLowerV2.Factorial.Main", "RiffleLowerV2.Factorial.MomentScales", "RiffleLowerV2.Factorial.PoissonPolynomial", "RiffleLowerV2.Factorial.PolynomialMoments", "RiffleLowerV2.Factorial.Ratios", "RiffleLowerV2.Factorial.Relative", "RiffleLowerV2.Factorial.RelativeFromExact", "RiffleLowerV2.Factorial.RelativeTargets", "RiffleLowerV2.Factorial.Requests", "RiffleLowerV2.Factorial.Residual", "RiffleLowerV2.Factorial.ResidualEstimates", "RiffleLowerV2.Localization.Bridge", "RiffleLowerV2.Localization.ColdSet", "RiffleLowerV2.Localization.Concentration", "RiffleLowerV2.Localization.Edges", "RiffleLowerV2.Localization.Endpoints.Check", "RiffleLowerV2.Localization.Endpoints.Coordinates", "RiffleLowerV2.Localization.Endpoints.Counts", "RiffleLowerV2.Localization.Endpoints.Error", "RiffleLowerV2.Localization.Endpoints.Means", "RiffleLowerV2.Localization.Endpoints.Partitions", "RiffleLowerV2.Localization.Endpoints.ProductWeights", "RiffleLowerV2.Localization.Endpoints", "RiffleLowerV2.Localization.EventBounds", "RiffleLowerV2.Localization.Events", "RiffleLowerV2.Localization.Geometry.Algebra", "RiffleLowerV2.Localization.Geometry.Bounds", "RiffleLowerV2.Localization.Geometry.Check", "RiffleLowerV2.Localization.Geometry.Consequences", "RiffleLowerV2.Localization.Geometry.Empirical", "RiffleLowerV2.Localization.Geometry.Rates", "RiffleLowerV2.Localization.Geometry", "RiffleLowerV2.Localization.Intervals", "RiffleLowerV2.Localization.Main", "RiffleLowerV2.Localization.Probability", "RiffleLowerV2.Localization.ProbabilityIntervals", "RiffleLowerV2.Localization.RankBarriers", "RiffleLowerV2.Localization.WordOrder", "RiffleLowerV2.Localization.Words", "RiffleLowerV2.MacroscopicLower.Main", "RiffleLowerV2.MacroscopicLower.Parameters", "RiffleLowerV2.Model.ComponentFibers", "RiffleLowerV2.Model.FiberCounts", "RiffleLowerV2.Model.FiniteLaws", "RiffleLowerV2.Model.GraphLaw", "RiffleLowerV2.Model.GraphSorting", "RiffleLowerV2.Model.Main", "RiffleLowerV2.Model.Physical", "RiffleLowerV2.Model.Sorting", "RiffleLowerV2.Occupancy.CentralModel", "RiffleLowerV2.Occupancy.CentralScales", "RiffleLowerV2.Occupancy.Check", "RiffleLowerV2.Occupancy.Conditional", "RiffleLowerV2.Occupancy.ConditionalInputs", "RiffleLowerV2.Occupancy.Covariance", "RiffleLowerV2.Occupancy.FiniteProbability", "RiffleLowerV2.Occupancy.Forcing", "RiffleLowerV2.Occupancy.Main", "RiffleLowerV2.Occupancy.Marginal", "RiffleLowerV2.Occupancy.MarginalNumerical", "RiffleLowerV2.Occupancy.ModelInputs", "RiffleLowerV2.Occupancy.Nonrare", "RiffleLowerV2.Occupancy.Numerical", "RiffleLowerV2.Occupancy.Poisson", "RiffleLowerV2.Occupancy.RarePair", "RiffleLowerV2.Occupancy.RegimeAlgebra", "RiffleLowerV2.Occupancy.Scales", "RiffleLowerV2.ProfileTransfer.Compat.Error", "RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature", "RiffleLowerV2.ProfileTransfer.Compat.IntegralEnvelope", "RiffleLowerV2.ProfileTransfer.Compat.LatticeCounts", "RiffleLowerV2.ProfileTransfer.Empirical", "RiffleLowerV2.ProfileTransfer.Endpoint", "RiffleLowerV2.ProfileTransfer.Extrema", "RiffleLowerV2.ProfileTransfer.Main", "RiffleLowerV2.ProfileTransfer.Margin", "RiffleLowerV2.ProfileTransfer.Parameters", "RiffleLowerV2.ProfileTransfer.Quadrature", "RiffleLowerV2.ProfileTransfer.Spatial", "RiffleLowerV2.Shared.Adapters", "RiffleLowerV2.Shared.Empirical", "RiffleLowerV2.Shared.Geometry", "RiffleLowerV2.Shared.Model", "RiffleLowerV2.Shared.Path", "RiffleLowerV2.Shared.Smoke", "RiffleLowerV2.Shared.Statistics", "RiffleLowerV2.Shared", "RiffleLowerV2.Thinning.AllPrefixes", "RiffleLowerV2.Thinning.Check", "RiffleLowerV2.Thinning.ColumnSampling", "RiffleLowerV2.Thinning.Compat.Check", "RiffleLowerV2.Thinning.Compat.Conditioning", "RiffleLowerV2.Thinning.Compat.FiniteLaw", "RiffleLowerV2.Thinning.Compat.Hypergeometric", "RiffleLowerV2.Thinning.Compat.HypergeometricConcentration", "RiffleLowerV2.Thinning.Compat.HypergeometricMoments", "RiffleLowerV2.Thinning.Compat.ResidualSampling", "RiffleLowerV2.Thinning.Compat.SamplingCheck", "RiffleLowerV2.Thinning.Compat.SubsetSampling", "RiffleLowerV2.Thinning.Compat.SubsetTransform", "RiffleLowerV2.Thinning.Main", "RiffleLowerV2.Thinning.MaximalWord", "RiffleLowerV2.Thinning.PMFTools", "RiffleLowerV2.Thinning.PrefixCoordinates", "RiffleLowerV2.Thinning.Prefixes", "RiffleLowerV2.Thinning.Process", "RiffleLowerV2.Thinning.Recursion", "RiffleLowerV2.Thinning.Residual.Check", "RiffleLowerV2.Thinning.Residual.Independence", "RiffleLowerV2.Thinning.Residual.IndependenceCheck", "RiffleLowerV2.Thinning.Residual.Prefix", "RiffleLowerV2.Thinning.Residual.PrefixCheck", "RiffleLowerV2.Thinning.Residual", "RiffleLowerV2.Thinning.Sampling", "RiffleLowerV2.Thinning.Tails", "RiffleLowerV2.Thinning.UniformError", "RiffleLowerV2.Types.Approximation", "RiffleLowerV2.Types.ClassEntropy", "RiffleLowerV2.Types.Construction", "RiffleLowerV2.Types.Counting", "RiffleLowerV2.Types.Empty", "RiffleLowerV2.Types.EntropyBounds", "RiffleLowerV2.Types.Main", "RiffleLowerV2.Types.MassBins", "RiffleLowerV2.Types.Partition", "RiffleLowerV2.Types.Rates", "RiffleLowerV2.Types.Rounding", "RiffleLowerV2.Types.Truncation", "RiffleLowerV2.Types.WordEstimates", "RiffleLowerV2.Witness.Continuous", "RiffleLowerV2.Witness.Empirical", "RiffleLowerV2.Witness.EmpiricalTilt", "RiffleLowerV2.Witness.Finite", "RiffleLowerV2.Witness.Main", "RiffleLowerV2.Witness.OneColumn", "RiffleLowerV2.Witness.OneColumnBasic", "RiffleLowerV2.Witness.Rounding", "RiffleLowerV2.Witness.Selection", "RiffleLowerV2"]
  for expected in requiredModules do
    unless env.header.moduleNames.any (fun n => n.toString == expected) do
      throwError "Required source module was not imported: {expected}"
  logInfo m!"IMPORTED_"Contracts.v1.AdditionalFinite", "Contracts.v1.Ascent", "Contracts.v1.AssemblyInputs", "Contracts.v1.Endpoints", "Contracts.v1.FactorialOccupancy", "Contracts.v1.ModelThinning", "Contracts.v1.TransferFinite", "Contracts.v1.WitnessGeometry", "Contracts.v1", "Contracts", "RiffleLowerV2.Ascent.Asymptotic", "RiffleLowerV2.Ascent.Components.Charging", "RiffleLowerV2.Ascent.Components.Clipping", "RiffleLowerV2.Ascent.Components", "RiffleLowerV2.Ascent.Concentration", "RiffleLowerV2.Ascent.Expectation", "RiffleLowerV2.Ascent.FiniteConsequences", "RiffleLowerV2.Ascent.FiniteProbability", "RiffleLowerV2.Ascent.MGF", "RiffleLowerV2.Ascent.Main", "RiffleLowerV2.Ascent.Mixture", "RiffleLowerV2.Ascent.Quantitative", "RiffleLowerV2.Ascent.RelativeOrder.Basic", "RiffleLowerV2.Ascent.RelativeOrder.Boundary", "RiffleLowerV2.Ascent.RelativeOrder.Check", "RiffleLowerV2.Ascent.RelativeOrder.Law", "RiffleLowerV2.Ascent.RelativeOrder.Weighted", "RiffleLowerV2.Ascent.RelativeOrder", "RiffleLowerV2.Ascent.Selection", "RiffleLowerV2.Ascent.Test", "RiffleLowerV2.Ascent.UniformBaseline", "RiffleLowerV2.Completed", "RiffleLowerV2.EmpiricalLower.Cold", "RiffleLowerV2.EmpiricalLower.CollisionMean", "RiffleLowerV2.EmpiricalLower.LargestAsymptotic.Numerical", "RiffleLowerV2.EmpiricalLower.LargestAsymptotic", "RiffleLowerV2.EmpiricalLower.LargestFinite", "RiffleLowerV2.EmpiricalLower.Main", "RiffleLowerV2.EmpiricalLower.ManyEdges", "RiffleLowerV2.EmpiricalLower.Scan", "RiffleLowerV2.Factorial.Basic", "RiffleLowerV2.Factorial.Bonferroni", "RiffleLowerV2.Factorial.Central", "RiffleLowerV2.Factorial.Exact", "RiffleLowerV2.Factorial.Main", "RiffleLowerV2.Factorial.MomentScales", "RiffleLowerV2.Factorial.PoissonPolynomial", "RiffleLowerV2.Factorial.PolynomialMoments", "RiffleLowerV2.Factorial.Ratios", "RiffleLowerV2.Factorial.Relative", "RiffleLowerV2.Factorial.RelativeFromExact", "RiffleLowerV2.Factorial.RelativeTargets", "RiffleLowerV2.Factorial.Requests", "RiffleLowerV2.Factorial.Residual", "RiffleLowerV2.Factorial.ResidualEstimates", "RiffleLowerV2.Localization.Bridge", "RiffleLowerV2.Localization.ColdSet", "RiffleLowerV2.Localization.Concentration", "RiffleLowerV2.Localization.Edges", "RiffleLowerV2.Localization.Endpoints.Check", "RiffleLowerV2.Localization.Endpoints.Coordinates", "RiffleLowerV2.Localization.Endpoints.Counts", "RiffleLowerV2.Localization.Endpoints.Error", "RiffleLowerV2.Localization.Endpoints.Means", "RiffleLowerV2.Localization.Endpoints.Partitions", "RiffleLowerV2.Localization.Endpoints.ProductWeights", "RiffleLowerV2.Localization.Endpoints", "RiffleLowerV2.Localization.EventBounds", "RiffleLowerV2.Localization.Events", "RiffleLowerV2.Localization.Geometry.Algebra", "RiffleLowerV2.Localization.Geometry.Bounds", "RiffleLowerV2.Localization.Geometry.Check", "RiffleLowerV2.Localization.Geometry.Consequences", "RiffleLowerV2.Localization.Geometry.Empirical", "RiffleLowerV2.Localization.Geometry.Rates", "RiffleLowerV2.Localization.Geometry", "RiffleLowerV2.Localization.Intervals", "RiffleLowerV2.Localization.Main", "RiffleLowerV2.Localization.Probability", "RiffleLowerV2.Localization.ProbabilityIntervals", "RiffleLowerV2.Localization.RankBarriers", "RiffleLowerV2.Localization.WordOrder", "RiffleLowerV2.Localization.Words", "RiffleLowerV2.MacroscopicLower.Main", "RiffleLowerV2.MacroscopicLower.Parameters", "RiffleLowerV2.Model.ComponentFibers", "RiffleLowerV2.Model.FiberCounts", "RiffleLowerV2.Model.FiniteLaws", "RiffleLowerV2.Model.GraphLaw", "RiffleLowerV2.Model.GraphSorting", "RiffleLowerV2.Model.Main", "RiffleLowerV2.Model.Physical", "RiffleLowerV2.Model.Sorting", "RiffleLowerV2.Occupancy.CentralModel", "RiffleLowerV2.Occupancy.CentralScales", "RiffleLowerV2.Occupancy.Check", "RiffleLowerV2.Occupancy.Conditional", "RiffleLowerV2.Occupancy.ConditionalInputs", "RiffleLowerV2.Occupancy.Covariance", "RiffleLowerV2.Occupancy.FiniteProbability", "RiffleLowerV2.Occupancy.Forcing", "RiffleLowerV2.Occupancy.Main", "RiffleLowerV2.Occupancy.Marginal", "RiffleLowerV2.Occupancy.MarginalNumerical", "RiffleLowerV2.Occupancy.ModelInputs", "RiffleLowerV2.Occupancy.Nonrare", "RiffleLowerV2.Occupancy.Numerical", "RiffleLowerV2.Occupancy.Poisson", "RiffleLowerV2.Occupancy.RarePair", "RiffleLowerV2.Occupancy.RegimeAlgebra", "RiffleLowerV2.Occupancy.Scales", "RiffleLowerV2.ProfileTransfer.Compat.Error", "RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature", "RiffleLowerV2.ProfileTransfer.Compat.IntegralEnvelope", "RiffleLowerV2.ProfileTransfer.Compat.LatticeCounts", "RiffleLowerV2.ProfileTransfer.Empirical", "RiffleLowerV2.ProfileTransfer.Endpoint", "RiffleLowerV2.ProfileTransfer.Extrema", "RiffleLowerV2.ProfileTransfer.Main", "RiffleLowerV2.ProfileTransfer.Margin", "RiffleLowerV2.ProfileTransfer.Parameters", "RiffleLowerV2.ProfileTransfer.Quadrature", "RiffleLowerV2.ProfileTransfer.Spatial", "RiffleLowerV2.Shared.Adapters", "RiffleLowerV2.Shared.Empirical", "RiffleLowerV2.Shared.Geometry", "RiffleLowerV2.Shared.Model", "RiffleLowerV2.Shared.Path", "RiffleLowerV2.Shared.Smoke", "RiffleLowerV2.Shared.Statistics", "RiffleLowerV2.Shared", "RiffleLowerV2.Thinning.AllPrefixes", "RiffleLowerV2.Thinning.Check", "RiffleLowerV2.Thinning.ColumnSampling", "RiffleLowerV2.Thinning.Compat.Check", "RiffleLowerV2.Thinning.Compat.Conditioning", "RiffleLowerV2.Thinning.Compat.FiniteLaw", "RiffleLowerV2.Thinning.Compat.Hypergeometric", "RiffleLowerV2.Thinning.Compat.HypergeometricConcentration", "RiffleLowerV2.Thinning.Compat.HypergeometricMoments", "RiffleLowerV2.Thinning.Compat.ResidualSampling", "RiffleLowerV2.Thinning.Compat.SamplingCheck", "RiffleLowerV2.Thinning.Compat.SubsetSampling", "RiffleLowerV2.Thinning.Compat.SubsetTransform", "RiffleLowerV2.Thinning.Main", "RiffleLowerV2.Thinning.MaximalWord", "RiffleLowerV2.Thinning.PMFTools", "RiffleLowerV2.Thinning.PrefixCoordinates", "RiffleLowerV2.Thinning.Prefixes", "RiffleLowerV2.Thinning.Process", "RiffleLowerV2.Thinning.Recursion", "RiffleLowerV2.Thinning.Residual.Check", "RiffleLowerV2.Thinning.Residual.Independence", "RiffleLowerV2.Thinning.Residual.IndependenceCheck", "RiffleLowerV2.Thinning.Residual.Prefix", "RiffleLowerV2.Thinning.Residual.PrefixCheck", "RiffleLowerV2.Thinning.Residual", "RiffleLowerV2.Thinning.Sampling", "RiffleLowerV2.Thinning.Tails", "RiffleLowerV2.Thinning.UniformError", "RiffleLowerV2.Types.Approximation", "RiffleLowerV2.Types.ClassEntropy", "RiffleLowerV2.Types.Construction", "RiffleLowerV2.Types.Counting", "RiffleLowerV2.Types.Empty", "RiffleLowerV2.Types.EntropyBounds", "RiffleLowerV2.Types.Main", "RiffleLowerV2.Types.MassBins", "RiffleLowerV2.Types.Partition", "RiffleLowerV2.Types.Rates", "RiffleLowerV2.Types.Rounding", "RiffleLowerV2.Types.Truncation", "RiffleLowerV2.Types.WordEstimates", "RiffleLowerV2.Witness.Continuous", "RiffleLowerV2.Witness.Empirical", "RiffleLowerV2.Witness.EmpiricalTilt", "RiffleLowerV2.Witness.Finite", "RiffleLowerV2.Witness.Main", "RiffleLowerV2.Witness.OneColumn", "RiffleLowerV2.Witness.OneColumnBasic", "RiffleLowerV2.Witness.Rounding", "RiffleLowerV2.Witness.Selection", "RiffleLowerV2"_JSON {(toJson (env.header.moduleNames.map Name.toString)).compress}"
  for (name, info) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => env.mainModule.toString
    let prefix := moduleName.splitOn "." |>.head!
    if prefix == "RiffleLowerV2" || prefix == "Contracts" ||
        prefix == "RiffleTimeProfile" || prefix == "RiffleShuffle" then
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom closure at {name}: {ax}"
      let typeDeps := info.type.getUsedConstants.map Name.toString
      let valueDeps := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants.map Name.toString
        | none => #[]
      let typ ← liftTermElabM <| Meta.ppExpr info.type
      let val ← match info.value? (allowOpaque := true) with
        | some value => do
            if info.isTheorem then pure "" else
              let v ← liftTermElabM <| Meta.ppExpr value
              pure v.pretty
        | none => pure ""
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | _ => "generated"
      let row := Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName),
        ("kind", toJson kind), ("type", toJson typ.pretty), ("value", toJson val),
        ("type_dependencies", toJson typeDeps), ("value_dependencies", toJson valueDeps),
        ("axioms", toJson (axs.map Name.toString))]
      logInfo m!"FULL_DECLARATION_JSON {row.compress}"
  for root in #[`RiffleLowerV2.EmpiricalLower.empiricalCombined,
      `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable,
      `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto] do
    let mut queue := #[root]
    let mut seen : NameSet := {}
    let mut axioms : Array String := #[]
    let mut allNames : Array String := #[]
    while !queue.isEmpty do
      let name := queue.back!
      queue := queue.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some ci := env.find? name | throwError "Missing recursive dependency {name}"
      let typeDeps := ci.type.getUsedConstants
      let valueDeps := match ci.value? (allowOpaque := true) with
        | some value => value.getUsedConstants
        | none => #[]
      queue := queue ++ typeDeps ++ valueDeps
      allNames := allNames.push name.toString
      match ci with
      | .axiomInfo _ =>
        unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
          throwError "Unexpected recursively reached axiom {name}"
        axioms := axioms.push name.toString
      | _ => pure ()
    let collected ← Lean.collectAxioms root
    let row := Json.mkObj [("root", toJson root.toString),
      ("reachable_count", toJson allNames.size), ("all_reachable_names", toJson allNames),
      ("recursive_axioms", toJson axioms), ("collect_axioms", toJson (collected.map Name.toString))]
    logInfo m!"ENDPOINT_CLOSURE_JSON {row.compress}"
  logInfo "FULL_PACKAGE_58_REQUIRED_THEOREMS_AND_CLOSURES_VERIFIED"

#print RiffleLowerV2.Targets.EmpiricalCombinedTarget
#print RiffleLowerV2.Targets.MacroscopicIntegrableTarget
#print RiffleLowerV2.ScalarIntegrable
