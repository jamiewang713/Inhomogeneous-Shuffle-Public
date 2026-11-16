import Shuffle.HypergeometricMoments

noncomputable section

namespace Shuffle
namespace HypergeomParams

theorem varianceFormula_lower (p : HypergeomParams) (hN : 2 ≤ p.population)
    {u a b : ℝ} (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmean : u ≤ p.mean)
    (hmarked : a ≤ 1 - (p.marked : ℝ) / p.population)
    (hdraws : b ≤ 1 - (p.draws : ℝ) / p.population) :
    u * a * b ≤ p.varianceFormula := by
  have hn : (2 : ℝ) ≤ p.population := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < p.population := by linarith
  have hn1 : (0 : ℝ) < (p.population : ℝ) - 1 := by linarith
  have hk : (p.marked : ℝ) ≤ p.population := by exact_mod_cast p.marked_le
  have hm : (p.draws : ℝ) ≤ p.population := by exact_mod_cast p.draws_le
  have hcK : 0 ≤ 1 - (p.marked : ℝ) / p.population :=
    sub_nonneg.mpr ((div_le_one hn0).2 hk)
  have hcm : 0 ≤ 1 - (p.draws : ℝ) / p.population :=
    sub_nonneg.mpr ((div_le_one hn0).2 hm)
  have hcorr : 1 ≤ (p.population : ℝ) / ((p.population : ℝ) - 1) :=
    (one_le_div hn1).2 (by linarith)
  have hfac : p.varianceFormula =
      p.mean * (1 - (p.marked : ℝ) / p.population) *
        (1 - (p.draws : ℝ) / p.population) *
        ((p.population : ℝ) / ((p.population : ℝ) - 1)) := by
    unfold varianceFormula mean
    field_simp
    <;> ring
  rw [hfac]
  have hprod : u * a * b ≤ p.mean * (1 - (p.marked : ℝ) / p.population) *
      (1 - (p.draws : ℝ) / p.population) :=
    mul_le_mul (mul_le_mul hmean hmarked ha p.mean_nonneg) hdraws hb
      (mul_nonneg p.mean_nonneg hcK)
  exact hprod.trans (le_mul_of_one_le_right
    (mul_nonneg (mul_nonneg p.mean_nonneg hcK) hcm) hcorr)

theorem variance_lower (p : HypergeomParams) (hN : 2 ≤ p.population)
    {u a b : ℝ} (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmean : u ≤ p.mean)
    (hmarked : a ≤ 1 - (p.marked : ℝ) / p.population)
    (hdraws : b ≤ 1 - (p.draws : ℝ) / p.population) :
    u * a * b ≤ p.law.variance (fun q => (q.val : ℝ)) := by
  rw [p.variance_val]
  exact p.varianceFormula_lower hN hu ha hb hmean hmarked hdraws

end HypergeomParams

theorem sample_complement_of_reserve {N r m h : ℝ}
    (hN : 0 < N) (hr0 : 0 ≤ r) (hr : r < N)
    (hm : 0 ≤ m) (hh : 0 ≤ h) (hreserve : m + r ≤ N - h) :
    h / N ≤ 1 - m / (N - r) := by
  have hn : 0 < N - r := sub_pos.mpr hr
  calc
    h / N ≤ h / (N - r) := div_le_div_of_nonneg_left hh hn (by linarith)
    _ ≤ (N - r - m) / (N - r) :=
      div_le_div_of_nonneg_right (by linarith) hn.le
    _ = 1 - m / (N - r) := by
      rw [sub_div, div_self (ne_of_gt hn)]

theorem residual_fraction_error {N r K s e : ℝ}
    (hN : 0 < N) (hr : r < N) (he : 0 ≤ e)
    (herr : |s - r * K / N| ≤ e) :
    |(K - s) / (N - r) - K / N| ≤ e / (N - r) := by
  have hn : 0 < N - r := sub_pos.mpr hr
  have hid : (K - s) / (N - r) - K / N = -(s - r * K / N) / (N - r) := by
    field_simp
    <;> ring
  rw [hid, abs_div, abs_neg, abs_of_pos hn]
  exact div_le_div_of_nonneg_right herr hn.le

end Shuffle
