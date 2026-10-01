import Contracts.v1.TransferFinite
import RiffleTimeProfile.Analysis

/-!
Spatial continuity and bounded probability integrals for LB07.
The max-cost continuity argument and the power-sum continuity argument are
extracted from the checked canonical `TimeProfile.exists_regular_partition`
proof in RiffleTimeProfile/Analysis.lean.  No time regularity is inferred here.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace RiffleLowerV2.ProfileTransfer
open TimeProfile

theorem continuous_prob {k : ℕ} (l : Fin k) :
    Continuous (fun p : Simplex k => prob p l) :=
  (continuous_apply l).comp continuous_subtype_val

theorem continuous_pileMax {k : ℕ} : Continuous (pileMax : Simplex k → ℝ) := by
  unfold pileMax
  exact NNReal.continuous_coe.comp (Continuous.finset_sup_apply
    (s := Finset.univ) (fun l _ =>
      (continuous_prob l).subtype_mk (fun p => prob_nonneg p l)))

theorem continuous_maxCost {k : ℕ} : Continuous (maxCost : Simplex k → ℝ) := by
  convert (continuous_pileMax.log (fun p => (pileMax_pos p).ne')).neg using 1
  ext p
  simp [maxCost, digitCost]

theorem continuous_psi {k : ℕ} {α : ℝ} (hα : α ∈ Icc (2 : ℝ) 4) :
    Continuous (fun p : Simplex k => psi p α) := by
  have hz : Continuous (fun p : Simplex k => powerSum p α) := by
    apply continuous_finsetSum
    intro l _
    exact (continuous_prob l).rpow continuous_const (fun _ => Or.inr (by linarith [hα.1]))
  exact (hz.log (fun p => (powerSum_pos p (by linarith [hα.1])).ne')).neg

theorem jointPsiContinuity : Targets.JointPsiContinuity := by
  intro k _hk
  have hz : ContinuousOn (fun z : Simplex k × ℝ => powerSum z.1 z.2)
      (univ ×ˢ Icc (2 : ℝ) 4) := by
    apply continuousOn_finsetSum
    intro l _
    exact ((continuous_prob l).comp continuous_fst).continuousOn.rpow
      continuous_snd.continuousOn
      (fun z hz => Or.inr (by have := hz.2.1; linarith))
  exact (hz.log (fun z hz =>
    (powerSum_pos z.1 (by have := hz.2.1; linarith)).ne')).neg

/-- Spatial continuity and a finite pointwise bound imply spatial integrability. -/
theorem integrable_of_continuous_bounded {k : ℕ}
    (ν : ProbabilityMeasure (Simplex k)) (f : Simplex k → ℝ) {M : ℝ}
    (hc : Continuous f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M) :
    Integrable f (ν : Measure (Simplex k)) := by
  apply Integrable.of_bound hc.aestronglyMeasurable M
  exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf p).1]
    using (hf p).2)

theorem integrable_maxCost {k : ℕ} (hk : 2 ≤ k)
    (ν : ProbabilityMeasure (Simplex k)) :
    Integrable maxCost (ν : Measure (Simplex k)) :=
  integrable_of_continuous_bounded ν maxCost continuous_maxCost (maxCost_bounds hk)

theorem integrable_psi {k : ℕ} (hk : 2 ≤ k)
    (ν : ProbabilityMeasure (Simplex k)) {α : ℝ} (hα : α ∈ Icc (2 : ℝ) 4) :
    Integrable (fun p => psi p α) (ν : Measure (Simplex k)) :=
  integrable_of_continuous_bounded ν (fun p => psi p α) (continuous_psi hα)
    (fun p => psi_bounds hk p hα)

theorem scalar_integral_bounds {k : ℕ}
    (ν : ProbabilityMeasure (Simplex k)) (f : Simplex k → ℝ) {M : ℝ}
    (hfint : Integrable f (ν : Measure (Simplex k)))
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M) :
    0 ≤ ∫ p, f p ∂(ν : Measure (Simplex k)) ∧
      ∫ p, f p ∂(ν : Measure (Simplex k)) ≤ M := by
  refine ⟨integral_nonneg (fun p => (hf p).1), ?_⟩
  have h := integral_mono hfint (integrable_const M) (fun p => (hf p).2)
  simpa using h

theorem profileMaxCost_bounds {k : ℕ} (hk : 2 ≤ k) (μ : TimeLaw k) (t : ℝ) :
    0 ≤ profileMaxCost μ t ∧ profileMaxCost μ t ≤ Real.log (k : ℝ) :=
  scalar_integral_bounds (μ t) maxCost (integrable_maxCost hk (μ t)) (maxCost_bounds hk)

theorem profilePsi_bounds {k : ℕ} (hk : 2 ≤ k) (μ : TimeLaw k) (t : ℝ)
    {α : ℝ} (hα : α ∈ Icc (2 : ℝ) 4) :
    0 ≤ profilePsi μ t α ∧ profilePsi μ t α ≤ 4 * Real.log (k : ℝ) :=
  scalar_integral_bounds (μ t) (fun p => psi p α) (integrable_psi hk (μ t) hα)
    (fun p => psi_bounds hk p hα)

end RiffleLowerV2.ProfileTransfer
