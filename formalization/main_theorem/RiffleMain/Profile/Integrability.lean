import RiffleMain.Profile.Definitions
import RiffleLowerV2.ProfileTransfer.Spatial
import Mathlib.Probability.Kernel.MeasurableIntegral

set_option autoImplicit false

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2.ProfileTransfer

/-- The manuscript's measurable family is a probability kernel. -/
def profileKernel {k : ℕ} {μ : TimeLaw k} (hμ : MeasurableProfile μ) :
    ProbabilityTheory.Kernel ℝ (Simplex k) :=
  ⟨fun t => (μ t : Measure (Simplex k)),
    Measure.measurable_of_measurable_coe _ hμ⟩

instance profileKernel_markov {k : ℕ} {μ : TimeLaw k} (hμ : MeasurableProfile μ) :
    ProbabilityTheory.IsMarkovKernel (profileKernel hμ) :=
  ⟨fun t => by change IsProbabilityMeasure (μ t : Measure (Simplex k)); infer_instance⟩

theorem measurable_profileIntegral {k : ℕ} {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) {f : Simplex k → ℝ} (hf : Measurable f) :
    Measurable (fun t => ∫ p, f p ∂(μ t : Measure (Simplex k))) := by
  exact (hf.stronglyMeasurable.integral_kernel
    (κ := profileKernel hμ)).measurable

theorem intervalIntegrable_of_measurable_bounded {f : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hb : ∀ t, |f t| ≤ M) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  constructor <;> apply Integrable.of_bound hf.aestronglyMeasurable M <;>
    exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using hb t)

theorem measurable_profileMaxCost {k : ℕ} {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) : Measurable (profileMaxCost μ) :=
  measurable_profileIntegral hμ continuous_maxCost.measurable

theorem measurable_profilePsi {k : ℕ} {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) {θ : ℝ} (hθ : θ ∈ Icc (2 : ℝ) 4) :
    Measurable (fun t => profilePsi μ t θ) :=
  measurable_profileIntegral hμ (continuous_psi hθ).measurable

theorem measurable_cellMass {k : ℕ} {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) (P : BorelPartition k) (i : Fin P.cellCount) :
    Measurable (cellMass μ P i) := by
  have hcell : MeasurableSet (P.cell i) :=
    P.measurable_classify (measurableSet_singleton i)
  exact (hμ (P.cell i) hcell).ennreal_toReal

/-- All scalar hypotheses used by the frozen transfer results follow from
measurability of the profile.  No convergence of partition-cell counts is used. -/
theorem scalarIntegrable {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) (P : BorelPartition k) (T : ℝ) :
    RiffleLowerV2.ScalarIntegrable μ P T := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply intervalIntegrable_of_measurable_bounded (measurable_cellMass hμ P i)
      (M := 1)
    intro t
    change |((μ t : Measure (Simplex k)) (P.cell i)).toReal| ≤ 1
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
      (prob_le_one : (μ t : Measure (Simplex k)) (P.cell i) ≤ 1)).trans_eq
        ENNReal.toReal_one
  · apply intervalIntegrable_of_measurable_bounded (measurable_profileMaxCost hμ)
      (M := Real.log (k : ℝ))
    intro t
    rw [abs_of_nonneg (profileMaxCost_bounds hk μ t).1]
    exact (profileMaxCost_bounds hk μ t).2
  · intro θ hθ
    apply intervalIntegrable_of_measurable_bounded (measurable_profilePsi hμ hθ)
      (M := 4 * Real.log (k : ℝ))
    intro t
    rw [abs_of_nonneg (profilePsi_bounds hk μ t hθ).1]
    exact (profilePsi_bounds hk μ t hθ).2

end RiffleMain.Profile
