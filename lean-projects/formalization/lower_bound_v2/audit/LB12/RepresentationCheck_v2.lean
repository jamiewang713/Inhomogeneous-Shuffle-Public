import RiffleLowerV2.MacroscopicLower.Main

noncomputable section

namespace RiffleLowerV2.LB12

theorem physicalInverseLaw_eq_map {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) :
    physicalInverseLaw cuts = (physicalForwardLaw cuts).map Equiv.symm := by
  rw [physicalInverseLaw, physicalForwardLaw, PMF.map_comp]
  rfl

theorem physicalInverse_forward_tv {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) =
      tv (physicalForwardLaw cuts) (uniformPermutation N) := by
  rw [physicalInverseLaw_eq_map]
  exact Model.inversionTV N (physicalForwardLaw cuts)

end RiffleLowerV2.LB12

#print axioms RiffleLowerV2.LB12.physicalInverseLaw_eq_map
#print axioms RiffleLowerV2.LB12.physicalInverse_forward_tv
