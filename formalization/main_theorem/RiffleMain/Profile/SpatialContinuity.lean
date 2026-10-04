import RiffleMain.Profile.UniformCumulative
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

theorem psi_uniform_theta {k : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ θ' : ℝ,
      θ ∈ Icc (2 : ℝ) 4 → θ' ∈ Icc (2 : ℝ) 4 → |θ-θ'| < δ →
      ∀ p : Simplex k, |psi p θ - psi p θ'| < ε := by
  let Theta := ↥(Icc (2 : ℝ) 4)
  have hz : Continuous (fun z : Simplex k × Theta => powerSum z.1 z.2) := by
    apply continuous_finsetSum
    intro l _
    exact ((continuous_prob l).comp continuous_fst).rpow
      (continuous_subtype_val.comp continuous_snd)
      (fun z => Or.inr (by have := z.2.property.1; linarith))
  have hp : Continuous (fun z : Simplex k × Theta => psi z.1 z.2) :=
    (hz.log (fun z => (powerSum_pos z.1 (by have := z.2.property.1; linarith)).ne')).neg
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hp) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro θ θ' hθ hθ' hdist p
  have hh := huc (a := (p, (⟨θ, hθ⟩ : Theta)))
    (b := (p, (⟨θ', hθ'⟩ : Theta)))
  have hd : dist (p, (⟨θ, hθ⟩ : Theta)) (p, (⟨θ', hθ'⟩ : Theta)) < δ := by
    simpa only [Prod.dist_eq, dist_self, Subtype.dist_eq, Real.dist_eq,
      max_eq_right (abs_nonneg (θ-θ'))] using hdist
  simpa only [Real.dist_eq] using hh hd

theorem empiricalCumulative_spatial_error {k N K : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k N K) {f g : Simplex k → ℝ} {χ T s : ℝ}
    (hχ : 0 ≤ χ) (hfg : ∀ p, |f p-g p| ≤ χ)
    (hs : s ∈ Icc 0 T) :
    |empiricalCumulative cuts (by omega) f s - empiricalCumulative cuts (by omega) g s| ≤ T*χ := by
  have hS : 0 ≤ horizon N K := div_nonneg (Nat.cast_nonneg _) (logScale_pos hN).le
  have hmin : min s (horizon N K) ∈ Icc 0 (horizon N K) :=
    ⟨le_min hs.1 hS, min_le_right _ _⟩
  have hh := empiricalIntegral_abs_le hN (fun j => hfg (cuts.profile (by omega) j))
    (show (0 : ℝ) ∈ Icc 0 (horizon N K) from ⟨le_rfl, hS⟩) hmin
  simp only [sub_zero, abs_of_nonneg hmin.1] at hh
  have heq : empiricalCumulative cuts (by omega) f s - empiricalCumulative cuts (by omega) g s =
      empiricalIntegral N (fun j => f (cuts.profile (by omega) j) - g (cuts.profile (by omega) j))
        0 (min s (horizon N K)) := by
    simp only [empiricalCumulative, empiricalIntegral, mul_sub, sub_div, Finset.sum_sub_distrib]
  rw [heq]
  exact hh.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans hs.2) hχ)

theorem profileCumulative_spatial_error {k : ℕ} {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) {f g : Simplex k → ℝ} {M χ T s : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfb : ∀ p, 0 ≤ f p ∧ f p ≤ M) (hgb : ∀ p, 0 ≤ g p ∧ g p ≤ M)
    (hχ : 0 ≤ χ) (hfg : ∀ p, |f p-g p| ≤ χ) (hs : s ∈ Icc 0 T) :
    |profileCumulative μ f s - profileCumulative μ g s| ≤ T*χ := by
  let qf := fun t => ∫ p, f p ∂(μ t : Measure (Simplex k))
  let qg := fun t => ∫ p, g p ∂(μ t : Measure (Simplex k))
  have hfi (t : ℝ) := integrable_of_continuous_bounded (μ t) f hf hfb
  have hgi (t : ℝ) := integrable_of_continuous_bounded (μ t) g hg hgb
  have hqfb (t : ℝ) := scalar_integral_bounds (μ t) f (hfi t) hfb
  have hqgb (t : ℝ) := scalar_integral_bounds (μ t) g (hgi t) hgb
  have hqfi : IntervalIntegrable qf volume 0 s :=
    intervalIntegrable_of_measurable_bounded (measurable_profileIntegral hμ hf.measurable)
      (fun t => by rw [abs_of_nonneg (hqfb t).1]; exact (hqfb t).2) 0 s
  have hqgi : IntervalIntegrable qg volume 0 s :=
    intervalIntegrable_of_measurable_bounded (measurable_profileIntegral hμ hg.measurable)
      (fun t => by rw [abs_of_nonneg (hqgb t).1]; exact (hqgb t).2) 0 s
  have hqbound (t : ℝ) : -χ ≤ qf t-qg t ∧ qf t-qg t ≤ χ := by
    have hupper := integral_mono (hfi t) ((hgi t).add (integrable_const χ))
      (fun p => by
        change f p ≤ g p + χ
        have := (abs_le.mp (hfg p)).2
        linarith)
    have hlower := integral_mono (hgi t) ((hfi t).add (integrable_const χ))
      (fun p => by
        change g p ≤ f p + χ
        have := (abs_le.mp (hfg p)).1
        linarith)
    change (∫ p, f p ∂(μ t : Measure (Simplex k))) ≤
      ∫ p, (g p + χ) ∂(μ t : Measure (Simplex k)) at hupper
    change (∫ p, g p ∂(μ t : Measure (Simplex k))) ≤
      ∫ p, (f p + χ) ∂(μ t : Measure (Simplex k)) at hlower
    simp only [integral_add (hgi t) (integrable_const χ),
      integral_add (hfi t) (integrable_const χ)] at hupper hlower
    simp at hupper hlower
    dsimp [qf, qg]
    constructor <;> linarith
  have hupper := intervalIntegral.integral_mono_on hs.1 (hqfi.sub hqgi)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => χ) volume 0 s)
    (fun t _ => (hqbound t).2)
  have hlower := intervalIntegral.integral_mono_on hs.1
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -χ) volume 0 s)
    (hqfi.sub hqgi) (fun t _ => (hqbound t).1)
  rw [intervalIntegral.integral_sub hqfi hqgi] at hupper hlower
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hupper hlower
  have hschi := mul_le_mul_of_nonneg_right hs.2 hχ
  change |(∫ t in 0..s, qf t) - (∫ t in 0..s, qg t)| ≤ _
  apply abs_le.mpr
  constructor <;> nlinarith

end RiffleMain.Profile
