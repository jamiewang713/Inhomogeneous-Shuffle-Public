import RiffleUpperV2.Exploration.HistoryProbability
import RiffleLowerV2.Thinning.Prefixes

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open RiffleLowerV2.Thinning

/-- Exact finite error sum for the prefix-size part of H. -/
def prefixSizeFailureSum {k n L : ℕ} (cuts : Cuts k n (L+1)) (ξ : ℝ) : ℝ :=
  ∑ x : Prefix k (L+1), if (n : ℝ)^ξ ≤ prefixMean cuts x then
    2 * Real.exp (-((prefixMean cuts x)^((2:ℝ)/3))^2 /
      (4 * (prefixMean cuts x + (prefixMean cuts x)^((2:ℝ)/3)))) else 0

/-- One actual prefix, retaining the certified denominator 4*(mu+t). -/
theorem prefixSizeConcentration {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (ξ : ℝ) (x : Prefix k (L+1)) (hx : (n : ℝ)^ξ ≤ prefixMean cuts x) :
    probability (fixedCountPMF cuts)
      (fun ω => (prefixMean cuts x)^((2:ℝ)/3) < |(prefixCount x ω : ℝ) - prefixMean cuts x|) ≤
      2 * Real.exp (-((prefixMean cuts x)^((2:ℝ)/3))^2 /
        (4 * (prefixMean cuts x + (prefixMean cuts x)^((2:ℝ)/3)))) := by
  have hμ : 0 < prefixMean cuts x :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) ξ).trans_le hx
  have ht : 0 < (prefixMean cuts x)^((2:ℝ)/3) := Real.rpow_pos_of_pos hμ _
  apply le_trans (probability_mono (fixedCountPMF cuts) (fun _ h => h.le))
  exact (prefixTails cuts hn x).1 _ ht

/-- The union is over every finite prefix, with no random choice or future information. -/
theorem allPrefixSizesConcentration {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n) (ξ : ℝ) :
    probability (fixedCountPMF cuts) (fun ω => ∃ x : Prefix k (L+1),
      (n : ℝ)^ξ ≤ prefixMean cuts x ∧
      (prefixMean cuts x)^((2:ℝ)/3) < |(prefixCount x ω : ℝ) - prefixMean cuts x|) ≤
        prefixSizeFailureSum cuts ξ := by
  apply le_trans (probability_iUnion_le (fixedCountPMF cuts) _)
  unfold prefixSizeFailureSum
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : (n : ℝ)^ξ ≤ prefixMean cuts x
  · simp only [hx, if_true, true_and]
    exact prefixSizeConcentration cuts hn ξ x hx
  · simp [hx, RiffleLowerV2.probability, RiffleLowerV2.expect]

/-- The denominator-4 Bernstein version gives the same stretched exponent, with c=1/8. -/
theorem bernstein_twoThirds_exponent {μ : ℝ} (hμ : 1 ≤ μ) :
    -((μ^((2:ℝ)/3))^2) / (4*(μ+μ^((2:ℝ)/3))) ≤ -μ^((1:ℝ)/3)/8 := by
  have hp : 0 < μ := lt_of_lt_of_le (by norm_num) hμ
  have ht : μ^((2:ℝ)/3) ≤ μ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hμ
      (by norm_num : (2:ℝ)/3 ≤ 1)
  have he : (μ^((2:ℝ)/3))^2 = μ*μ^((1:ℝ)/3) := by
    calc
      _ = μ^(((2:ℝ)/3)*2) := by rw [Real.rpow_mul hp.le]; norm_num
      _ = μ^((1:ℝ)+(1:ℝ)/3) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hp, Real.rpow_one]
  have hd : 0 < 4*(μ+μ^((2:ℝ)/3)) := by positivity
  have hq := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hp.le ((1:ℝ)/3))
  apply (div_le_div_iff₀ hd (by norm_num : (0:ℝ)<8)).2
  rw [he]
  nlinarith

/-- Explicit polynomial prefix cost with a stretched-exponential error. -/
theorem prefixSizeFailureSum_le {k n L : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0 < n) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    prefixSizeFailureSum cuts ξ ≤
      2 * (L+2 : ℕ) * (k : ℝ)^(L+1) * Real.exp (-(n : ℝ)^(ξ/3)/8) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnξ : 1 ≤ (n : ℝ)^ξ := Real.one_le_rpow hn1 hξ
  have heach (x : Prefix k (L+1)) :
      (if (n : ℝ)^ξ ≤ prefixMean cuts x then
        2*Real.exp (-((prefixMean cuts x)^((2:ℝ)/3))^2 /
          (4*(prefixMean cuts x+(prefixMean cuts x)^((2:ℝ)/3)))) else 0) ≤
        2*Real.exp (-(n : ℝ)^(ξ/3)/8) := by
    split_ifs with hx
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      apply (bernstein_twoThirds_exponent (hnξ.trans hx)).trans
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg hn0 ξ) hx (by norm_num : (0:ℝ)≤1/3)
      rw [← Real.rpow_mul hn0] at hh
      have hexp : ξ*((1:ℝ)/3) = ξ/3 := by ring
      rw [hexp] at hh
      linarith
    · positivity
  unfold prefixSizeFailureSum
  calc
    _ ≤ ∑ _ : Prefix k (L+1), 2*Real.exp (-(n : ℝ)^(ξ/3)/8) :=
      Finset.sum_le_sum (fun x _ => heach x)
    _ = (Fintype.card (Prefix k (L+1)) : ℝ) * (2*Real.exp (-(n : ℝ)^(ξ/3)/8)) := by simp
    _ ≤ (((L+2)*k^(L+1) : ℕ) : ℝ) * (2*Real.exp (-(n : ℝ)^(ξ/3)/8)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast prefix_card_le_of_cuts cuts hn
    _ = _ := by push_cast; ring

end RiffleUpperV2.Exploration
