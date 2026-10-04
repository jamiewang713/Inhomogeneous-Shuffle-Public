import RiffleMain.Profile.Integrability
import RiffleMain.Profile.TimeCut

set_option autoImplicit false

noncomputable section
open Set MeasureTheory
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2.ProfileTransfer

theorem scalar_timeCut_error {q : ℝ → ℝ} {M T s δ : ℝ}
    (hq : Measurable q) (hb : ∀ t, 0 ≤ q t ∧ q t ≤ M)
    (hM : 0 ≤ M) (hδ : 0 < δ) (hs : 0 ≤ s) (hsT : s ≤ T) :
    |(∫ t in 0..s, q t) - (∫ t in 0..T, q t * timeCut s δ t)| ≤ M*δ := by
  let v := max 0 (s-δ)
  let g := fun t => q t * timeCut s δ t
  have hg : Measurable g := hq.mul (timeCut_continuous s δ).measurable
  have hgb (t : ℝ) : 0 ≤ g t ∧ g t ≤ M := by
    refine ⟨mul_nonneg (hb t).1 (timeCut_bounds _ _ _).1, ?_⟩
    calc
      _ ≤ q t * 1 := mul_le_mul_of_nonneg_left (timeCut_bounds _ _ _).2 (hb t).1
      _ ≤ M := by simpa using (hb t).2
  have hqi (a b : ℝ) : IntervalIntegrable q volume a b :=
    intervalIntegrable_of_measurable_bounded hq
      (fun t => by rw [abs_of_nonneg (hb t).1]; exact (hb t).2) a b
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b :=
    intervalIntegrable_of_measurable_bounded hg
      (fun t => by rw [abs_of_nonneg (hgb t).1]; exact (hgb t).2) a b
  have hv0 : 0 ≤ v := le_max_left _ _
  have hvs : v ≤ s := max_le hs (by linarith)
  have hgap : s-v ≤ δ := by have := le_max_right 0 (s-δ); change s-δ ≤ v at this; linarith
  have htail : (∫ t in s..T, g t) = 0 := by
    calc
      _ = ∫ _t in s..T, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hsT] at ht
        simp only [g, timeCut_eq_zero hδ ht.1, mul_zero]
      _ = 0 := by simp
  have hwhole : (∫ t in 0..T, g t) = ∫ t in 0..s, g t := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hgi 0 s) (hgi s T)
    rw [htail, add_zero] at hh
    exact hh.symm
  have hprefix : (∫ t in 0..v, g t) = ∫ t in 0..v, q t := by
    by_cases hv : s-δ ≤ 0
    · simp [v, max_eq_left hv]
    · have hveq : v = s-δ := max_eq_right (not_le.mp hv).le
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hv0] at ht
      have ht' : t ≤ s-δ := ht.2.trans_eq hveq
      simp only [g, timeCut_eq_one hδ ht', mul_one]
  have hlo : (∫ t in 0..v, q t) ≤ ∫ t in 0..T, g t := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hgi 0 v) (hgi v s)
    rw [hprefix] at hh
    rw [hwhole]
    have hp := intervalIntegral.integral_nonneg_of_forall (μ := volume) hvs (fun t => (hgb t).1)
    linarith
  have hhi : (∫ t in 0..T, g t) ≤ ∫ t in 0..s, q t := by
    rw [hwhole]
    apply intervalIntegral.integral_mono_on hs (hgi 0 s) (hqi 0 s)
    intro t _
    exact (mul_le_mul_of_nonneg_left (timeCut_bounds _ _ _).2 (hb t).1).trans_eq (mul_one _)
  have hbound : (∫ t in v..s, q t) ≤ M*(s-v) := by
    have hh := intervalIntegral.integral_mono_on hvs (hqi v s)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume v s)
      (fun t _ => (hb t).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hqi 0 v) (hqi v s)
  change |(∫ t in 0..s, q t) - (∫ t in 0..T, g t)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hhi)]
  have hh := mul_le_mul_of_nonneg_left hgap hM
  linarith

theorem profile_timeCut_error {k : ℕ} {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) {f : Simplex k → ℝ} {M T s δ : ℝ}
    (hf : Continuous f) (hb : ∀ p, 0 ≤ f p ∧ f p ≤ M)
    (hM : 0 ≤ M) (hδ : 0 < δ) (hs : 0 ≤ s) (hsT : s ≤ T) :
    |(∫ t in 0..s, ∫ p, f p ∂(μ t : Measure (Simplex k))) -
      profileTest μ T (fun z => f z.1 * timeCut s δ z.2)| ≤ M*δ := by
  have hq := measurable_profileIntegral hμ hf.measurable
  have hqb (t : ℝ) := scalar_integral_bounds (μ t) f
    (integrable_of_continuous_bounded (μ t) f hf hb) hb
  simpa only [profileTest, integral_mul_const] using
    scalar_timeCut_error hq hqb hM hδ hs hsT

end RiffleMain.Profile
