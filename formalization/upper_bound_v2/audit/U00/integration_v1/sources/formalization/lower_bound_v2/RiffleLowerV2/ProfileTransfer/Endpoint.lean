import RiffleLowerV2.ProfileTransfer.Empirical

noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2.ProfileTransfer
open TimeProfile

theorem gridTime_floor_bounds {N K : ℕ} (hN : 2 ≤ N) {t : ℝ}
    (ht0 : 0 ≤ t) (htK : t ≤ horizon N K) :
    gridTime N ⌊t * logScale N⌋₊ ∈ Icc (0 : ℝ) (horizon N K) ∧
    0 ≤ t - gridTime N ⌊t * logScale N⌋₊ ∧
    t - gridTime N ⌊t * logScale N⌋₊ ≤ 1 / logScale N := by
  have he := horizonDepth_error hN ht0
  have hL := logScale_pos hN
  change 0 ≤ t - gridTime N ⌊t * logScale N⌋₊ ∧
    t - gridTime N ⌊t * logScale N⌋₊ < 1 / logScale N at he
  exact ⟨⟨by unfold gridTime; positivity,
    (sub_nonneg.mp he.1).trans htK⟩, he.1, he.2.le⟩

/-- Arbitrary endpoint interpolation differs from right-endpoint samples by two columns. -/
theorem empiricalIntegral_sample_error {K N : ℕ} (hN : 2 ≤ N)
    {f : Fin K → ℝ} {M r s : ℝ} (hM : 0 ≤ M) (hf : ∀ j, |f j| ≤ M)
    (hr0 : 0 ≤ r) (hrs : r ≤ s) (hsK : s ≤ horizon N K) :
    |empiricalIntegral N f r s -
      (∑ j ∈ Finset.univ.filter (fun j : Fin K =>
        r < columnTime N j ∧ columnTime N j ≤ s), f j) / logScale N| ≤
      2 * M / logScale N := by
  classical
  have hL := logScale_pos hN
  have hs0 := hr0.trans hrs
  have hrK := hrs.trans hsK
  have hrf := gridTime_floor_bounds hN hr0 hrK
  have hsf := gridTime_floor_bounds hN hs0 hsK
  have horder : ⌊r * logScale N⌋₊ ≤ ⌊s * logScale N⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right hrs hL.le)
  have hgrid := empiricalIntegral_grid hN f _ _ horder
  have heq : gridSum N f ⌊r * logScale N⌋₊ ⌊s * logScale N⌋₊ =
      (∑ j ∈ Finset.univ.filter (fun j : Fin K =>
        r < columnTime N j ∧ columnTime N j ≤ s), f j) / logScale N := by
    unfold gridSum
    congr 2
    apply Finset.filter_congr
    intro j _
    simp only [columnTime, lt_div_iff₀ hL, div_le_iff₀ hL]
    have ha : r * logScale N < (j.val : ℝ) + 1 ↔ ⌊r * logScale N⌋₊ < j.val + 1 := by
      rw [Nat.floor_lt (mul_nonneg hr0 hL.le)]
      norm_cast
    have hb : (j.val : ℝ) + 1 ≤ s * logScale N ↔ j.val + 1 ≤ ⌊s * logScale N⌋₊ := by
      rw [Nat.le_floor_iff (mul_nonneg hs0 hL.le)]
      norm_cast
    rw [ha, hb]
    omega
  rw [← heq, ← hgrid]
  calc
    _ ≤ (|r - gridTime N ⌊r * logScale N⌋₊| +
        |s - gridTime N ⌊s * logScale N⌋₊|) * M :=
      empiricalIntegral_endpoint_bound hN hf ⟨hr0, hrK⟩ ⟨hs0, hsK⟩ hrf.1 hsf.1
    _ ≤ (1 / logScale N + 1 / logScale N) * M := by
      rw [abs_of_nonneg hrf.2.1, abs_of_nonneg hsf.2.1]
      exact mul_le_mul_of_nonneg_right (add_le_add hrf.2.2 hsf.2.2) hM
    _ = 2 * M / logScale N := by ring

end RiffleLowerV2.ProfileTransfer
