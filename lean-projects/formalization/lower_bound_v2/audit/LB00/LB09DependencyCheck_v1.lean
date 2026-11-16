import RiffleLowerV2.Thinning.Main
import RiffleLowerV2.Witness.Main
import RiffleLowerV2.Types.Main
import RiffleLowerV2.Model.Sorting

example : RiffleLowerV2.Targets.SuccessiveThinning := RiffleLowerV2.Thinning.successiveThinning
example : RiffleLowerV2.Targets.PrefixTails := RiffleLowerV2.Thinning.prefixTails
example : RiffleLowerV2.Targets.AllPrefixConcentration := RiffleLowerV2.Thinning.allPrefixConcentration
example : RiffleLowerV2.Targets.PrefixFailureUniform := RiffleLowerV2.Thinning.prefixFailureUniform
example : RiffleLowerV2.Targets.ResidualLaw := RiffleLowerV2.Thinning.residualLaw
example : RiffleLowerV2.Targets.HypergeometricTransform := RiffleLowerV2.Thinning.hypergeometricTransform
example : RiffleLowerV2.Targets.MaximalMeanIdentity := RiffleLowerV2.Thinning.maximalMeanIdentity
example : RiffleLowerV2.Targets.OneColumnTiltTarget := RiffleLowerV2.Witness.oneColumnTilt
example : RiffleLowerV2.Targets.EmpiricalTiltTarget := RiffleLowerV2.Witness.empiricalTilt
example : RiffleLowerV2.Targets.ColdWitnessTarget := RiffleLowerV2.Witness.coldWitness
example : RiffleLowerV2.Targets.LB05Target := RiffleLowerV2.Witness.lB05
example : RiffleLowerV2.Targets.RoundedTypeTarget := RiffleLowerV2.Types.roundedType
example : RiffleLowerV2.Targets.PrefixRanks := RiffleLowerV2.Model.prefixRanks

#print axioms RiffleLowerV2.Thinning.successiveThinning
#print axioms RiffleLowerV2.Thinning.prefixTails
#print axioms RiffleLowerV2.Thinning.allPrefixConcentration
#print axioms RiffleLowerV2.Thinning.prefixFailureUniform
#print axioms RiffleLowerV2.Thinning.residualLaw
#print axioms RiffleLowerV2.Thinning.hypergeometricTransform
#print axioms RiffleLowerV2.Thinning.maximalMeanIdentity
#print axioms RiffleLowerV2.Witness.oneColumnTilt
#print axioms RiffleLowerV2.Witness.empiricalTilt
#print axioms RiffleLowerV2.Witness.coldWitness
#print axioms RiffleLowerV2.Witness.lB05
#print axioms RiffleLowerV2.Types.roundedType
#print axioms RiffleLowerV2.Model.prefixRanks
