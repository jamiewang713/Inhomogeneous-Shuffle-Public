import RiffleUpperV2.Shared.FirstMomentAPI
import RiffleUpperV2.Contracts.V1.Empirical
import RiffleUpperV2.Contracts.V1.Profile
import RiffleLowerV2.Thinning.Main
import RiffleLowerV2.Factorial.Exact
import RiffleLowerV2.ProfileTransfer.Main

set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs false
#check @RiffleLowerV2.Model.physical_graph_representation
#check @RiffleLowerV2.Model.expect_bind
#check @RiffleLowerV2.Model.columnIndependence
#check @RiffleLowerV2.Model.columnMarginal
#check @RiffleLowerV2.Model.shuffle_componentSort_fiber_card_eq
#check @RiffleLowerV2.Thinning.prefixTransform
#check @RiffleLowerV2.Thinning.prefixTails
#check @RiffleLowerV2.Thinning.residualPrefixTransform
#check @RiffleLowerV2.Thinning.residualPrefixTails
#check @RiffleLowerV2.Factorial.exactJointFactorial
#print RiffleLowerV2.Targets.ExactJointFactorial
#check @RiffleLowerV2.ProfileTransfer.genericQuadrature
#print RiffleLowerV2.Targets.GenericQuadrature
#check @InhomogeneousShuffle.FirstMoment.expectedCommonEdges_eq_sum_sq
#check @InhomogeneousShuffle.FirstMoment.expectedCommonEdges_power_bound
#print RiffleUpperV2.Contracts.V1.F
#print RiffleUpperV2.Contracts.V1.E
#print RiffleUpperV2.Contracts.V1.P
#print RiffleUpperV2.Contracts.V1.T
#print RiffleUpperV2.Contracts.V1.RProfile
#print RiffleUpperV2.Contracts.V1.REmpirical
#print axioms RiffleUpperV2.physical_graph_representation
#print axioms RiffleUpperV2.expectedCommonEdges_eq_sum_sq
#print axioms RiffleUpperV2.empiricalInf_attained
#print axioms RiffleUpperV2.criticalTime_empty
#print axioms RiffleUpperV2.mixingTime_empty
#print axioms RiffleLowerV2.Thinning.residualPrefixTransform
#print axioms RiffleLowerV2.Thinning.residualPrefixTails
#print axioms RiffleLowerV2.Factorial.exactJointFactorial
#print axioms RiffleLowerV2.ProfileTransfer.genericQuadrature
