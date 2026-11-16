import RiffleMain.Profile.Definitions
import RiffleLowerV2.ProfileTransfer.Empirical

set_option autoImplicit false

noncomputable section
open Set
open scoped BigOperators
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

/-- A continuous approximation from below to the indicator of the past. -/
def timeCut (s δ t : ℝ) : ℝ := max 0 (min 1 ((s-t)/δ))

theorem timeCut_continuous (s δ : ℝ) : Continuous (timeCut s δ) :=
  continuous_const.max (continuous_const.min
    ((continuous_const.sub continuous_id).div_const δ))

theorem timeCut_bounds (s δ t : ℝ) : 0 ≤ timeCut s δ t ∧ timeCut s δ t ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem timeCut_mono {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Monotone (fun s => timeCut s δ t) := by
  intro a b hab
  exact max_le_max_left _ (min_le_min_left _
    (div_le_div_of_nonneg_right (sub_le_sub_right hab _) hδ.le))

theorem timeCut_eq_zero {s δ t : ℝ} (hδ : 0 < δ) (hst : s ≤ t) :
    timeCut s δ t = 0 := by
  unfold timeCut
  apply max_eq_left
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hst) hδ.le)

theorem timeCut_eq_one {s δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ s-δ) :
    timeCut s δ t = 1 := by
  unfold timeCut
  rw [min_eq_left ((le_div_iff₀ hδ).2 (by linarith))]
  norm_num

theorem columnFraction_zero {N K : ℕ} (j : Fin K) : columnFraction N j 0 = 0 := by
  unfold columnFraction
  simp only [zero_mul, zero_sub]
  exact max_eq_left ((min_le_right _ _).trans (neg_nonpos.mpr (Nat.cast_nonneg _)))

theorem columnFraction_bounds {N K : ℕ} (j : Fin K) (s : ℝ) :
    0 ≤ columnFraction N j s ∧ columnFraction N j s ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem timeCut_le_columnFraction {N K : ℕ} (hN : 2 ≤ N)
    (j : Fin K) {s δ : ℝ} (hδ : 0 < δ) :
    timeCut s δ (columnTime N j) ≤ columnFraction N j s := by
  by_cases hjs : columnTime N j ≤ s
  · have hL := logScale_pos hN
    have hj : (j.val : ℝ) + 1 ≤ s * logScale N := (div_le_iff₀ hL).mp hjs
    have hw : columnFraction N j s = 1 := by
      unfold columnFraction
      rw [min_eq_left (by linarith)]
      norm_num
    rw [hw]
    exact (timeCut_bounds _ _ _).2
  · rw [timeCut_eq_zero hδ (not_le.mp hjs).le]
    exact (columnFraction_bounds j s).1

theorem columnFraction_le_timeCut {N K : ℕ} (hN : 2 ≤ N)
    (j : Fin K) {s δ : ℝ} (hδ : 0 < δ) :
    columnFraction N j (max 0 (s-δ-1/logScale N)) ≤ timeCut s δ (columnTime N j) := by
  have hL := logScale_pos hN
  by_cases hs : s-δ-1/logScale N ≤ 0
  · rw [max_eq_left hs, columnFraction_zero]
    exact (timeCut_bounds _ _ _).1
  · rw [max_eq_right (not_le.mp hs).le]
    by_cases hj : (s-δ-1/logScale N)*logScale N ≤ (j.val : ℝ)
    · have hw : columnFraction N j (s-δ-1/logScale N) = 0 := by
        unfold columnFraction
        exact max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr hj))
      rw [hw]
      exact (timeCut_bounds _ _ _).1
    · have htime : columnTime N j ≤ s-δ := by
        apply (div_le_iff₀ hL).2
        have hh := not_le.mp hj
        have he : (s-δ-1/logScale N)*logScale N = (s-δ)*logScale N-1 := by
          field_simp [hL.ne']
        rw [he] at hh
        linarith
      rw [timeCut_eq_one hδ htime]
      exact (columnFraction_bounds j _).2

/-- Continuous time tests approximate the interpolated empirical cumulative
integral uniformly, with only one-column rounding loss. -/
theorem empirical_timeCut_error {k N K : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k N K) {f : Simplex k → ℝ} {M s δ : ℝ}
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M) (hM : 0 ≤ M)
    (hδ : 0 < δ) (hs : 0 ≤ s) (hsK : s ≤ horizon N K) :
    |empiricalIntegral N (fun j => f (cuts.profile (by omega) j)) 0 s -
      empiricalTest cuts (by omega) (fun z => f z.1 * timeCut s δ z.2)| ≤
      M * (δ + 1/logScale N) := by
  let u := max 0 (s-δ-1/logScale N)
  let F : Fin K → ℝ := fun j => f (cuts.profile (by omega) j)
  let E := empiricalTest cuts (by omega) (fun z => f z.1 * timeCut s δ z.2)
  have hL := logScale_pos hN
  have hu0 : 0 ≤ u := le_max_left _ _
  have hus : u ≤ s := max_le hs (by have := one_div_pos.mpr hL; linarith)
  have hgap : s-u ≤ δ+1/logScale N := by
    have hh : s-δ-1/logScale N ≤ u := le_max_right _ _
    linarith
  have hupper : E ≤ empiricalIntegral N F 0 s := by
    unfold E empiricalTest empiricalIntegral
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro j _
    rw [columnFraction_zero, sub_zero]
    apply div_le_div_of_nonneg_right _ hL.le
    simpa only [F, mul_comm] using mul_le_mul_of_nonneg_right
      (timeCut_le_columnFraction hN j (s := s) hδ)
      (hf (cuts.profile (by omega) j)).1
  have hlower : empiricalIntegral N F 0 u ≤ E := by
    unfold E empiricalTest empiricalIntegral
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro j _
    rw [columnFraction_zero, sub_zero]
    apply div_le_div_of_nonneg_right _ hL.le
    simpa only [F, u, mul_comm] using mul_le_mul_of_nonneg_right
      (columnFraction_le_timeCut hN j (s := s) hδ)
      (hf (cuts.profile (by omega) j)).1
  have hsplit := empiricalIntegral_add N F 0 u s
  have hbound := empiricalIntegral_le hN (f := F) (M := M)
    (fun j => (hf _).2) hu0 hus hsK
  change |empiricalIntegral N F 0 s - E| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hupper)]
  have hb := mul_le_mul_of_nonneg_left hgap hM
  nlinarith

/-- The same estimate at a fixed macroscopic time, including the short interval
between the last column and the horizon. -/
theorem empirical_timeCut_error_clipped {k N K : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k N K) {f : Simplex k → ℝ} {M s δ : ℝ}
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M) (hM : 0 ≤ M)
    (hδ : 0 < δ) (hs : 0 ≤ s) :
    |empiricalIntegral N (fun j => f (cuts.profile (by omega) j)) 0
        (min s (horizon N K)) -
      empiricalTest cuts (by omega) (fun z => f z.1 * timeCut s δ z.2)| ≤
      M * (δ + 1/logScale N) := by
  by_cases hsK : s ≤ horizon N K
  · simpa only [min_eq_left hsK] using
      empirical_timeCut_error hN cuts hf hM hδ hs hsK
  · have hKs := (not_le.mp hsK).le
    rw [min_eq_right hKs]
    let F : Fin K → ℝ := fun j => f (cuts.profile (by omega) j)
    let E := fun t => empiricalTest cuts (by omega) (fun z => f z.1 * timeCut t δ z.2)
    have hL := logScale_pos hN
    have hS : 0 ≤ horizon N K := div_nonneg (Nat.cast_nonneg _) hL.le
    have hbase := empirical_timeCut_error hN cuts hf hM hδ hS le_rfl
    have hmono : E (horizon N K) ≤ E s := by
      unfold E empiricalTest
      apply div_le_div_of_nonneg_right _ hL.le
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (timeCut_mono hδ _ hKs) (hf _).1
    have htop : E s ≤ empiricalIntegral N F 0 (horizon N K) := by
      unfold E empiricalTest empiricalIntegral
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro j _
      rw [columnFraction_zero, sub_zero]
      have hw : columnFraction N j (horizon N K) = 1 := by
        have hj : (j.val : ℝ) + 1 ≤ (K : ℝ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
        unfold columnFraction horizon
        rw [div_mul_cancel₀ _ hL.ne', min_eq_left (by linarith)]
        norm_num
      rw [hw, one_mul]
      apply div_le_div_of_nonneg_right _ hL.le
      simpa using mul_le_mul_of_nonneg_left (timeCut_bounds s δ _).2 (hf _).1
    change |empiricalIntegral N F 0 (horizon N K) - E s| ≤ _
    rw [abs_of_nonneg (sub_nonneg.mpr htop)]
    have hh := (abs_le.mp hbase).2
    change empiricalIntegral N F 0 (horizon N K) - E (horizon N K) ≤ _ at hh
    linarith

end RiffleMain.Profile
