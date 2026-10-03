import RiffleUpperV2.Shared.Model
import FirstMoment.Assembly

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2
open InhomogeneousShuffle.FirstMoment

/-- Concrete primary-law adapter to the older generic aggregation API. -/
def toFirstMomentLaw {k n L : ℕ} (cuts : Cuts k n L) :
    FiniteGraphLaw (Sample cuts) (Fin (n-1)) where
  weight ω := (fixedCountPMF cuts ω).toReal
  weight_nonneg _ := ENNReal.toReal_nonneg
  weight_sum := by
    rw [← ENNReal.toReal_sum (fun ω _ => (fixedCountPMF cuts).apply_ne_top ω)]
    have h := (fixedCountPMF cuts).tsum_coe
    rw [tsum_fintype] at h
    simp [h]
  graph := shuffleEdges

theorem toFirstMomentLaw_expected {k n L : ℕ} (cuts : Cuts k n L) :
    (toFirstMomentLaw cuts).expectedCommonEdges = expectedCommonEdges cuts := by
  simp only [FiniteGraphLaw.expectedCommonEdges, toFirstMomentLaw, expectedCommonEdges,
    RiffleLowerV2.expect, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ω' _
  congr 2
  congr 1
  apply congrArg Finset.card
  apply Finset.ext
  intro e
  simp only [Finset.mem_inter]

/-- Aggregation identity only: it contains no concrete edge-density bound. -/
theorem expectedCommonEdges_eq_sum_sq {k n L : ℕ} (cuts : Cuts k n L) :
    expectedCommonEdges cuts = ∑ e, (toFirstMomentLaw cuts).edgeMarginal e ^ 2 := by
  rw [← toFirstMomentLaw_expected]
  exact InhomogeneousShuffle.FirstMoment.expectedCommonEdges_eq_sum_sq _

end RiffleUpperV2
