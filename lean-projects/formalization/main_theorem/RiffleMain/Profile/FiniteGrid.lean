import RiffleMain.Profile.Cumulative

set_option autoImplicit false

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

def timeGrid (T δ : ℝ) : Finset ℝ :=
  (Finset.range (⌊T/δ⌋₊+1)).image (fun i : ℕ => (i : ℝ)*δ)

theorem timeGrid_zero (T δ : ℝ) : 0 ∈ timeGrid T δ := by
  classical
  exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩

theorem timeGrid_mem {T δ s : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hs : s ∈ timeGrid T δ) : s ∈ Icc 0 T := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
  have hi' : i ≤ ⌊T/δ⌋₊ := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi
  have hfloor := Nat.floor_le (div_nonneg hT hδ.le)
  have hic : (i : ℝ) ≤ (⌊T/δ⌋₊ : ℝ) := by exact_mod_cast hi'
  exact ⟨mul_nonneg (Nat.cast_nonneg _) hδ.le,
    (le_div_iff₀ hδ).mp (hic.trans hfloor)⟩

theorem timeGrid_near {T δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc 0 T) :
    ∃ s ∈ timeGrid T δ, 0 ≤ t-s ∧ t-s < δ := by
  classical
  let i := ⌊t/δ⌋₊
  have hi : i < ⌊T/δ⌋₊+1 := Nat.lt_succ_of_le
    (Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hδ.le))
  refine ⟨(i : ℝ)*δ, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩, ?_, ?_⟩
  · have hh := Nat.floor_le (div_nonneg ht.1 hδ.le)
    have hh' := (le_div_iff₀ hδ).mp hh
    exact sub_nonneg.mpr hh'
  · have hh := Nat.lt_floor_add_one (t/δ)
    have hh' := (div_lt_iff₀ hδ).mp hh
    dsimp [i]
    nlinarith

theorem abs_min_sub_min_le (a b c : ℝ) : |min a c - min b c| ≤ |a-b| := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr (min_le_min_right c hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    by_cases hca : c ≤ a
    · rw [min_eq_right hca, min_eq_right (hca.trans hab)]
      linarith
    · rw [min_eq_left (not_le.mp hca).le]
      have hh := min_le_left b c
      linarith
  · rw [abs_sub_comm a b, abs_sub_comm (min a c) (min b c)]
    rw [abs_of_nonpos (sub_nonpos.mpr (min_le_min_right c hba)),
      abs_of_nonpos (sub_nonpos.mpr hba)]
    by_cases hcb : c ≤ b
    · rw [min_eq_right hcb, min_eq_right (hcb.trans hba)]
      linarith
    · rw [min_eq_left (not_le.mp hcb).le]
      have hh := min_le_left a c
      linarith

theorem empiricalCumulative_lipschitz {k N K : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k N K) {f : Simplex k → ℝ} {M s t : ℝ}
    (hf : ∀ p, |f p| ≤ M) (hM : 0 ≤ M) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |empiricalCumulative cuts (by omega) f s - empiricalCumulative cuts (by omega) f t| ≤
      |s-t| * M := by
  have hS : 0 ≤ horizon N K := div_nonneg (Nat.cast_nonneg _) (logScale_pos hN).le
  have hh := empiricalIntegral_endpoint_bound hN (fun j => hf (cuts.profile (by omega) j))
    (show (0 : ℝ) ∈ Icc 0 (horizon N K) from ⟨le_rfl, hS⟩)
    (show min s (horizon N K) ∈ Icc 0 (horizon N K) from
      ⟨le_min hs hS, min_le_right _ _⟩)
    (show (0 : ℝ) ∈ Icc 0 (horizon N K) from ⟨le_rfl, hS⟩)
    (show min t (horizon N K) ∈ Icc 0 (horizon N K) from
      ⟨le_min ht hS, min_le_right _ _⟩)
  simp only [sub_self, abs_zero, zero_add] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (abs_min_sub_min_le s t _) hM)

theorem profileCumulative_lipschitz {k : ℕ} {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) {f : Simplex k → ℝ} {M s t : ℝ}
    (hf : Continuous f) (hb : ∀ p, 0 ≤ f p ∧ f p ≤ M) :
    |profileCumulative μ f s - profileCumulative μ f t| ≤ |s-t| * M := by
  let q := fun t => ∫ p, f p ∂(μ t : Measure (Simplex k))
  have hqb (t : ℝ) := scalar_integral_bounds (μ t) f
    (integrable_of_continuous_bounded (μ t) f hf hb) hb
  have hqi (a b : ℝ) : IntervalIntegrable q volume a b :=
    intervalIntegrable_of_measurable_bounded (measurable_profileIntegral hμ hf.measurable)
      (fun t => by rw [abs_of_nonneg (hqb t).1]; exact (hqb t).2) a b
  have hforward (a b : ℝ) (hab : a ≤ b) :
      |profileCumulative μ f a - profileCumulative μ f b| ≤ (b-a)*M := by
    have hspl := intervalIntegral.integral_add_adjacent_intervals (hqi 0 a) (hqi a b)
    have hpos := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab (fun t => (hqb t).1)
    have hbound := intervalIntegral.integral_mono_on hab (hqi a b)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume a b)
      (fun t _ => (hqb t).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hbound
    change |(∫ t in 0..a, q t) - (∫ t in 0..b, q t)| ≤ _
    rw [abs_of_nonpos (by linarith)]
    linarith
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hforward s t hst
  · rw [abs_sub_comm]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using hforward t s hts

end RiffleMain.Profile
