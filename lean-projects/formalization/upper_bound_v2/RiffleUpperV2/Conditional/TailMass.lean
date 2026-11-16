import RiffleUpperV2.Margins.Empirical
import RiffleUpperV2.Conditional.RefinementCount
import RiffleLowerV2.Thinning.PrefixCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open TimeProfile RiffleLowerV2.Thinning

/-- The maximal mass of an unrestricted completion of a prefix. -/
def maximalTailMass {k n K : ℕ} (cuts : Cuts k n K) (hn : 0 < n) (x : Prefix k K) : ℝ :=
  ∏ j : Fin K, if j.val < x.1.val then 1 else pileMax (cuts.profile hn j)

theorem maximalTailMass_pos {k n K : ℕ} (cuts : Cuts k n K) (hn : 0 < n) (x : Prefix k K) :
    0 < maximalTailMass cuts hn x := by
  apply Finset.prod_pos
  intro j _
  split_ifs
  · norm_num
  · exact pileMax_pos _

/-- Prefix mass times maximal tail mass is bounded by the maximal full-word mean. -/
theorem prefixMean_mul_maximalTail_le {k n K : ℕ} (cuts : Cuts k n K) (hn : 0 < n)
    (x : Prefix k K) :
    prefixMean cuts x * maximalTailMass cuts hn x ≤ RiffleLowerV2.maximalMean cuts hn := by
  unfold prefixMean RiffleLowerV2.prefixMean RiffleLowerV2.maximalMean maximalTailMass
  rw [mul_assoc,← prefixColumnFraction_product,← Finset.prod_mul_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.prod_le_prod
  · intro j _
    apply mul_nonneg (prefixColumnFraction_bounds cuts hn x j).1
    split_ifs
    · norm_num
    · exact (pileMax_pos _).le
  · intro j _
    unfold prefixColumnFraction
    split_ifs with hj
    · simpa only [mul_one, Cuts.profile, prob] using prob_le_pileMax (cuts.profile hn j) (x.2.get ⟨j.val,hj⟩)
    · simp

theorem tailColumnCount {K r : ℕ} (hr : r ≤ K) :
    (Finset.univ.filter fun j : Fin K => ¬ j.val < r).card = K-r := by
  let f : {j : Fin K // ¬ j.val < r} → Fin (K-r) := fun j => ⟨j.val.val-r,by have := j.val.isLt; have := j.property; omega⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Subtype.ext
      apply Fin.ext
      have h := congrArg Fin.val hij
      dsimp [f] at h
      have := i.property
      have := j.property
      omega
    · intro j
      refine ⟨⟨⟨r+j.val,by have := j.isLt; omega⟩,by simp⟩,?_⟩
      apply Fin.ext
      simp [f]
  rw [← Fintype.card_subtype]
  exact (Fintype.card_of_bijective hf).trans (Fintype.card_fin _)

/-- Even a short tail with zero-count digits has maximal mass at least
k to minus its number of remaining columns. -/
theorem maximalTailMass_lower {k n K : ℕ} (hk : 0 < k) (cuts : Cuts k n K)
    (hn : 0 < n) (x : Prefix k K) :
    (1/(k : ℝ))^(K-x.1.val) ≤ maximalTailMass cuts hn x := by
  have he : (1/(k : ℝ))^(K-x.1.val) =
      ∏ j : Fin K, if j.val<x.1.val then 1 else 1/(k : ℝ) := by
    rw [Finset.prod_ite]
    have hc := tailColumnCount (Nat.le_of_lt_succ x.1.isLt)
    simp only [not_lt] at hc
    simp [hc]
  rw [he]
  apply Finset.prod_le_prod
  · intro j _; split_ifs <;> positivity
  · intro j _
    split_ifs
    · rfl
    · exact inv_card_le_pileMax hk _

/-- Finite late-short-suffix bound before the logarithmic window is inserted. -/
theorem shortPrefixMean_le {k n K N b : ℕ} (hk : 0 < k) (hN : 2 ≤ N)
    (cuts : Cuts k n K) (hn : 0 < n) (x : Prefix k K) (hb : K-x.1.val ≤ b)
    {η : ℝ} (hmargin : empiricalBeta N 0 cuts hn K ≤ -η) :
    prefixMean cuts x ≤ (k : ℝ)^b*(N : ℝ)^(-η) := by
  have htail := maximalTailMass_lower hk cuts hn x
  have hmax := (prefixMean_mul_maximalTail_le cuts hn x).trans
    (Margins.maximalMean_le_of_terminalMargin hN 0 cuts hn (by simpa using hmargin))
  have hmu : 0 ≤ prefixMean cuts x := by
    unfold prefixMean RiffleLowerV2.prefixMean RiffleLowerV2.prefixMass
    positivity
  have hl := (mul_le_mul_of_nonneg_left htail hmu).trans hmax
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : 0 < (k : ℝ)^(K-x.1.val) := pow_pos hk0 _
  rw [one_div_pow, one_div, mul_inv_le_iff₀ hp0] at hl
  calc
    _ ≤ (N : ℝ)^(-η)*(k : ℝ)^(K-x.1.val) := hl
    _ ≤ (N : ℝ)^(-η)*(k : ℝ)^b :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast hk) hb) (by positivity)
    _ = _ := mul_comm _ _

/-- The late-tail mean has the source rho*log k loss with the original log N. -/
theorem lateShortMean_le {k n K N : ℕ} (hk : 1 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k n K) (hn : 0 < n) (x : Prefix k K) {η ρ : ℝ} (hρ : 0 ≤ ρ)
    (hshort : K-x.1.val ≤ Exploration.windowLength N ρ)
    (hmargin : empiricalBeta N 0 cuts hn K ≤ -η) :
    prefixMean cuts x ≤ (k : ℝ)^2*(N : ℝ)^(-η+ρ*Real.log (k : ℝ)) := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
  calc
    _ ≤ (k : ℝ)^(Exploration.windowLength N ρ)*(N : ℝ)^(-η) :=
      shortPrefixMean_le hk hN cuts hn x hshort hmargin
    _ ≤ ((k : ℝ)^2*(N : ℝ)^(ρ*Real.log (k : ℝ)))*(N : ℝ)^(-η) :=
      mul_le_mul_of_nonneg_right (window_power_le hk (by omega) hρ) (by positivity)
    _ = _ := by rw [Real.rpow_add hn0]; ring

end RiffleUpperV2.Conditional
