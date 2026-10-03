import RiffleLowerV2.Thinning.Compat.HypergeometricConcentration
import RiffleLowerV2.Thinning.Compat.ResidualSampling

noncomputable section
open scoped BigOperators

namespace RiffleLowerV2.Thinning.Compat

variable {α : Type*} [DecidableEq α]

/-- The actual uniform subset count law transfers every finite expectation. -/
theorem sample_expect_intersection_eq_hypergeom (V A : Finset α) (m : ℕ)
    (hm : m ≤ V.card) (hA : A ⊆ V) (f : ℕ → ℝ) :
    (sampleLaw V m hm).expect (fun S => f (A ∩ S.val).card) =
      (samplingParams V A m hA hm).law.expect (fun q => f q.val) := by
  exact FiniteLaw.expect_eq_of_count_law (sampleLaw V m hm)
    (fun S => (A ∩ S.val).card) m (samplingParams V A m hA hm).law
    (sample_intersection_law V A m hA hm) f

/-- All-positive-s transform for an arbitrary fixed marked set and an actual
uniform fixed-size subset; the empty population is also covered. -/
theorem sample_expect_pow_intersection_le (V A : Finset α) (m : ℕ)
    (hm : m ≤ V.card) (hA : A ⊆ V) {s : ℝ} (hs : 0 < s) :
    (sampleLaw V m hm).expect (fun S => s ^ (A ∩ S.val).card) ≤
      (1 - (m : ℝ) / V.card + ((m : ℝ) / V.card) * s) ^ A.card := by
  rw [sample_expect_intersection_eq_hypergeom V A m hm hA]
  exact (samplingParams V A m hA hm).expect_pow_le_all hs

end RiffleLowerV2.Thinning.Compat
