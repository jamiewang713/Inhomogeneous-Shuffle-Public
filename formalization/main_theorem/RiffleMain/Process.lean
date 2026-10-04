import RiffleMain.Main
import RiffleMain.ProcessModel

set_option autoImplicit false

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace RiffleMain
open TimeProfile RiffleLowerV2

theorem randomizedProfileLike_of_sequence {k : ℕ} (μ : Profile.NonnegativeTimeLaw k)
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (ν : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (ν N)]
    (X : ∀ N, Ω N → RiffleUpperV2.InfiniteCuts k N)
    (hX : ∀ N K, Measurable (fun ω => (X N ω).take K))
    (hweak : RandomizedSequenceLike μ ν X) :
    RandomizedProfileLike μ (fun N K => finiteCutLaw (ν N) (X N) K (hX N K)) := by
  intro T hT f hf ε hε
  simpa only [finiteCutLaw_probability] using hweak T hT f hf ε hε

/-- The main theorem directly for infinite random cut sequences on arbitrary
probability spaces, with independent uniform interleavings conditional on cuts
encoded by the chronological physical law inside `randomForwardLaw`. -/
theorem main_random_sequence {k : ℕ} (hk : 2 ≤ k) (μ : Profile.NonnegativeTimeLaw k)
    (hμ : Profile.NonnegativeMeasurableProfile μ)
    (hnd : Profile.LocallyNondegenerate (Profile.extendNonnegativeProfile μ))
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (ν : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (ν N)]
    (X : ∀ N, Ω N → RiffleUpperV2.InfiniteCuts k N)
    (hX : ∀ N K, Measurable (fun ω => (X N ω).take K))
    (hweak : RandomizedSequenceLike μ ν X)
    (T : ℝ) (hT : 0 < T) (hne : ENNReal.ofReal T ≠ criticalTime μ) :
    Tendsto (fun N => tv (RandomLower.randomForwardLaw
      (finiteCutLaw (ν N) (X N) (horizonDepth N T) (hX N (horizonDepth N T))))
      (uniformPermutation N)) atTop
      (𝓝 (if ENNReal.ofReal T < criticalTime μ then 1 else 0)) :=
  main hk μ hμ hnd _ (randomizedProfileLike_of_sequence μ ν X hX hweak) T hT hne

/-- Both finite-critical-time limits for the original random sequence. -/
theorem cutoff_random_sequence {k : ℕ} (hk : 2 ≤ k) (μ : Profile.NonnegativeTimeLaw k)
    (hμ : Profile.NonnegativeMeasurableProfile μ)
    (hnd : Profile.LocallyNondegenerate (Profile.extendNonnegativeProfile μ))
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (ν : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (ν N)]
    (X : ∀ N, Ω N → RiffleUpperV2.InfiniteCuts k N)
    (hX : ∀ N K, Measurable (fun ω => (X N ω).take K))
    (hweak : RandomizedSequenceLike μ ν X)
    (hfinite : criticalTime μ ≠ ⊤) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun N => tv (RandomLower.randomForwardLaw
      (finiteCutLaw (ν N) (X N) (horizonDepth N ((1-ε)*(criticalTime μ).toReal))
        (hX N (horizonDepth N ((1-ε)*(criticalTime μ).toReal)))))
      (uniformPermutation N)) atTop (𝓝 1) ∧
    Tendsto (fun N => tv (RandomLower.randomForwardLaw
      (finiteCutLaw (ν N) (X N) (horizonDepth N ((1+ε)*(criticalTime μ).toReal))
        (hX N (horizonDepth N ((1+ε)*(criticalTime μ).toReal)))))
      (uniformPermutation N)) atTop (𝓝 0) :=
  cutoff hk μ hμ hnd _ (randomizedProfileLike_of_sequence μ ν X hX hweak)
    hfinite hε hε1

/-- Every finite positive horizon stays unmixed when the critical time is infinite. -/
theorem infinite_critical_random_sequence {k : ℕ} (hk : 2 ≤ k)
    (μ : Profile.NonnegativeTimeLaw k) (hμ : Profile.NonnegativeMeasurableProfile μ)
    (hnd : Profile.LocallyNondegenerate (Profile.extendNonnegativeProfile μ))
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (ν : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (ν N)]
    (X : ∀ N, Ω N → RiffleUpperV2.InfiniteCuts k N)
    (hX : ∀ N K, Measurable (fun ω => (X N ω).take K))
    (hweak : RandomizedSequenceLike μ ν X)
    (hinfinite : criticalTime μ = ⊤) (T : ℝ) (hT : 0 < T) :
    Tendsto (fun N => tv (RandomLower.randomForwardLaw
      (finiteCutLaw (ν N) (X N) (horizonDepth N T) (hX N (horizonDepth N T))))
      (uniformPermutation N)) atTop (𝓝 1) :=
  infinite_critical hk μ hμ hnd _ (randomizedProfileLike_of_sequence μ ν X hX hweak)
    hinfinite T hT

/-- Total variation at `floor (T log N)` for the averaged chronological shuffle. -/
def sequenceTV {k : ℕ} {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (ν : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (ν N)]
    (X : ∀ N, Ω N → RiffleUpperV2.InfiniteCuts k N)
    (hX : ∀ N K, Measurable (fun ω => (X N ω).take K)) (N : ℕ) (T : ℝ) : ℝ :=
  tv (RandomLower.randomForwardLaw
    (finiteCutLaw (ν N) (X N) (horizonDepth N T) (hX N (horizonDepth N T))))
    (uniformPermutation N)

/-- All assertions of the current manuscript's Theorem 1.1 in one declaration. -/
theorem theorem_1_1 {k : ℕ} (hk : 2 ≤ k) (μ : Profile.NonnegativeTimeLaw k)
    (hμ : Profile.NonnegativeMeasurableProfile μ)
    (hnd : Profile.LocallyNondegenerate (Profile.extendNonnegativeProfile μ))
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (ν : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (ν N)]
    (X : ∀ N, Ω N → RiffleUpperV2.InfiniteCuts k N)
    (hX : ∀ N K, Measurable (fun ω => (X N ω).take K))
    (hweak : RandomizedSequenceLike μ ν X) :
    (∀ T : ℝ, 0 < T → ENNReal.ofReal T ≠ criticalTime μ →
      Tendsto (fun N => sequenceTV ν X hX N T) atTop
        (𝓝 (if ENNReal.ofReal T < criticalTime μ then 1 else 0))) ∧
    (criticalTime μ ≠ ⊤ → ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun N => sequenceTV ν X hX N ((1-ε)*(criticalTime μ).toReal))
        atTop (𝓝 1) ∧
      Tendsto (fun N => sequenceTV ν X hX N ((1+ε)*(criticalTime μ).toReal))
        atTop (𝓝 0)) ∧
    (criticalTime μ = ⊤ → ∀ T : ℝ, 0 < T →
      Tendsto (fun N => sequenceTV ν X hX N T) atTop (𝓝 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT hne
    exact main_random_sequence hk μ hμ hnd ν X hX hweak T hT hne
  · intro hfinite ε hε hε1
    exact cutoff_random_sequence hk μ hμ hnd ν X hX hweak hfinite hε hε1
  · intro hinfinite T hT
    exact infinite_critical_random_sequence hk μ hμ hnd ν X hX hweak hinfinite T hT

end RiffleMain
