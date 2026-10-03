import RiffleUpperV2.Conditional.TailMass
import RiffleUpperV2.Reservoir.CollisionPower

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open TimeProfile Reservoir

/-- For a probability vector, one factor of p is summed exactly; only the
remaining positive power is bounded by the largest coordinate. -/
theorem powerSum_le_max_power {k : ℕ} (p : Simplex k) {q : ℝ} (hq : 1 < q) :
    (∑ a : Fin k, (prob p a)^q) ≤ (pileMax p)^(q-1) := by
  calc
    _ ≤ ∑ a : Fin k, prob p a * (pileMax p)^(q-1) := by
      apply Finset.sum_le_sum
      intro a _
      have he : (prob p a)^q = prob p a * (prob p a)^(q-1) := by
        nth_rw 1 [show q = 1+(q-1) by ring]
        rw [Real.rpow_add' (prob_nonneg p a) (by linarith),Real.rpow_one]
      rw [he]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (prob_nonneg p a) (prob_le_pileMax p a) (by linarith)) (prob_nonneg p a)
    _ = _ := by rw [← Finset.sum_mul,sum_prob,one_mul]

/-- The actual reservoir tail collision product is controlled by maximal
tail mass. This retains collision information in the near-unit size regime. -/
theorem tailPowerMass_le_maximalTail {k n K : ℕ} (cuts : Cuts k n K) (hn : 0 < n)
    (x : Prefix k K) {q : ℝ} (hq : 1 < q) :
    tailPowerMass cuts x q ≤ (maximalTailMass cuts hn x)^(q-1) := by
  unfold maximalTailMass tailPowerMass
  rw [← Real.finsetProd_rpow _ _ (by intro j _; split_ifs; norm_num; exact (pileMax_pos _).le)]
  apply Finset.prod_le_prod
  · intro j _
    split_ifs
    · norm_num
    · exact Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (by positivity) _)
  · intro j _
    change (if j.val < x.1.val then 1 else ∑ a : Fin k, ((cuts.count j a : ℝ)/n)^q) ≤ _
    split_ifs
    · simp
    · simpa only [Cuts.profile,prob] using powerSum_le_max_power (cuts.profile hn j) hq

/-- If a prefix mean exceeds N^-xi, terminal control bounds its remaining
maximal-word mass by N^(-eta+xi). -/
theorem intermediate_maximalTail_le {k n K N : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k n K) (hn : 0 < n) (x : Prefix k K) {η ξ : ℝ}
    (hmu : (N : ℝ)^(-ξ) ≤ prefixMean cuts x)
    (hmargin : empiricalBeta N 0 cuts hn K ≤ -η) :
    maximalTailMass cuts hn x ≤ (N : ℝ)^(-η+ξ) := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hprod := (mul_le_mul_of_nonneg_right hmu (maximalTailMass_pos cuts hn x).le).trans
    ((prefixMean_mul_maximalTail_le cuts hn x).trans
      (Margins.maximalMean_le_of_terminalMargin hN 0 cuts hn (by simpa using hmargin)))
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hn0 (-ξ))).mp
  apply hprod.trans_eq
  rw [← Real.rpow_add hn0]
  congr 1
  ring

end RiffleUpperV2.Conditional
