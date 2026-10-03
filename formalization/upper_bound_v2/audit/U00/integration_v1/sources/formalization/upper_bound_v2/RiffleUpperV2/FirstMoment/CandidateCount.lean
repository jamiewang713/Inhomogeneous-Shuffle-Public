import RiffleUpperV2.FirstMoment.DensityAggregation
import RiffleUpperV2.Shared.FiniteFiberCounts

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization

/-- Every actual descriptor fiber injects into its literal future prefixes. -/
theorem retainedCandidate_count {k n d N : ℕ} (hk : 0<k) (hN : 2≤N)
    (cuts : Cuts k n d) (hn : 0<n) (R : Fin k → Finset (Fin n))
    (T C chi delta width : ℝ) (hchi : 0<chi) (hchi1 : chi≤1)
    (hchiK : chi≤1/(k : ℝ)) (hwidth : 0<width) (hd : (d : ℝ)≤T*logScale N) :
    Fintype.card (RetainedAtPile hk N cuts hn R C chi delta hchiK) ≤
      (retainedClasses hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd).card *
        ((d+1)*k^d) := by
  let desc := retainedDescriptor hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd
  have h := card_le_image_card_mul_of_fiber_bound desc Finset.univ ((d+1)*k^d) ?_
  · simpa only [Finset.card_univ,desc,retainedClasses] using h
  intro key hkey
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hkey
  rw [← classPrefixes_card hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd t]
  exact (Finset.card_le_univ _).trans (prefix_card_bound k d hk)

end RiffleUpperV2.FirstMoment
