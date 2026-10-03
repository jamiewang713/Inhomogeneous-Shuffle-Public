import RiffleUpperV2.FirstMoment.EdgeSlots

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric RiffleLowerV2.Thinning

section Error
variable {k n d N : ℕ} (hk : 0<k) (cuts : Cuts k n (d+1)) (hn : 0<n)
    (c : ColumnAssignments cuts 0) (C chi delta : ℝ) (hchiK : chi≤1/(k : ℝ))
local notation "future" => tailCuts cuts
local notation "R" => (fun a : Fin k => anchorRows c a)
local notation "bad" => discardedMarginal (N := N) hk cuts hn c C chi delta hchiK

/-- A discarded marginal is a sum of k actual probabilities. -/
theorem discardedMarginal_bounds (m : ℤ) : 0≤bad m ∧ bad m≤k := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ => probability_nonneg _ _)
  · calc
      _ ≤ ∑ _ : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => probability_at_most_one _ _)
      _ = _ := by simp

/-- The total discarded graph mass is controlled by actual discarded rows in each pile. -/
theorem discardedMarginal_total (B : ℝ)
    (hB : ∀ p : Fin k, expect (fixedCountPMF future) (fun omega =>
      ((FirstMoment.rowsInWords (R p)
        (discardedWords hk N future hn (R p) C chi delta hchiK) omega).card : ℝ))≤B) :
    (∑ e : Fin (n-1), bad e.val)≤(k : ℝ)*B := by
  change (∑ e : Fin (n-1), ∑ p : Fin k, _)≤_
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ p : Fin k, B := by
      apply Finset.sum_le_sum
      intro p _
      have h := (discardedEdges_total_le_discardedRows (N := N) hk future hn (R p) C chi delta hchiK
        (firstPileStart cuts p) (edgeSlots n)).trans (hB p)
      simpa only [sum_edgeSlots] using h
    _ = _ := by simp

/-- Squaring the discarded-pile sum costs only the fixed factor k. -/
theorem discardedMarginal_squares (B : ℝ)
    (hB : ∀ p : Fin k, expect (fixedCountPMF future) (fun omega =>
      ((FirstMoment.rowsInWords (R p)
        (discardedWords hk N future hn (R p) C chi delta hchiK) omega).card : ℝ))≤B) :
    (∑ e : Fin (n-1), bad e.val ^ 2)≤(k : ℝ)^2*B := by
  calc
    _ ≤ ∑ e : Fin (n-1), (k : ℝ)*bad e.val := by
      apply Finset.sum_le_sum
      intro e _
      have h := discardedMarginal_bounds (N := N) hk cuts hn c C chi delta hchiK e.val
      nlinarith
    _ = (k : ℝ)*(∑ e : Fin (n-1),bad e.val) := by rw [Finset.mul_sum]
    _ ≤ (k : ℝ)*((k : ℝ)*B) := mul_le_mul_of_nonneg_left
      (discardedMarginal_total hk cuts hn c C chi delta hchiK B hB) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Literal discarded plus omitted-block errors have the required finite square sum. -/
theorem graphError_squares (B z : ℝ)
    (hB : ∀ p : Fin k, expect (fixedCountPMF future) (fun omega =>
      ((FirstMoment.rowsInWords (R p)
        (discardedWords hk N future hn (R p) C chi delta hchiK) omega).card : ℝ))≤B) :
    (∑ e : Fin (n-1), (bad e.val+z)^2)≤2*(k : ℝ)^2*B+2*(n-1 : ℕ)*z^2 := by
  calc
    _ ≤ ∑ e : Fin (n-1), (2*bad e.val^2+2*z^2) := by
      apply Finset.sum_le_sum
      intro e _
      nlinarith [sq_nonneg (bad e.val-z)]
    _ = 2*(∑ e : Fin (n-1),bad e.val^2)+2*(n-1 : ℕ)*z^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp
      <;> ring
    _ ≤ _ := by
      have h := discardedMarginal_squares hk cuts hn c C chi delta hchiK B hB
      linarith

end Error
end RiffleUpperV2.FirstMoment
