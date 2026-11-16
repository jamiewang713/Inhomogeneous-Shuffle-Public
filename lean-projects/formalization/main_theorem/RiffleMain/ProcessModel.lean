import RiffleMain.Profile.Definitions
import RiffleMain.Profile.NonnegativeTime
import RiffleTimeProfile.Source
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Adapter from arbitrary probability spaces and infinite random cut sequences
to the finite marginal formulation. The source probability spaces need not be
discrete or shared between deck sizes. -/
set_option autoImplicit false

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace RiffleMain
open TimeProfile RiffleLowerV2

theorem probability_eq_toMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (Q : PMF α) (A : α → Prop) :
    probability Q A = (Q.toMeasure {x | A x}).toReal := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · unfold probability expect
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : A x <;> simp [hx]
  · intro x _
    by_cases hx : A x <;> simp [hx, PMF.apply_ne_top]

/-- Distribution of a finite prefix of an arbitrary random cut sequence. -/
def finiteCutLaw {k N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : Ω → RiffleUpperV2.InfiniteCuts k N) (K : ℕ)
    (hX : Measurable (fun ω => (X ω).take K)) : PMF (Cuts k N K) := by
  letI : IsProbabilityMeasure (ν.map (fun ω => (X ω).take K)) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  exact (ν.map (fun ω => (X ω).take K)).toPMF

theorem finiteCutLaw_toMeasure {k N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : Ω → RiffleUpperV2.InfiniteCuts k N) (K : ℕ)
    (hX : Measurable (fun ω => (X ω).take K)) :
    (finiteCutLaw ν X K hX).toMeasure = ν.map (fun ω => (X ω).take K) := by
  simp [finiteCutLaw]

theorem finiteCutLaw_probability {k N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : Ω → RiffleUpperV2.InfiniteCuts k N) (K : ℕ)
    (hX : Measurable (fun ω => (X ω).take K)) (A : Cuts k N K → Prop) :
    probability (finiteCutLaw ν X K hX) A =
      (ν {ω | A ((X ω).take K)}).toReal := by
  rw [probability_eq_toMeasure, finiteCutLaw_toMeasure,
    Measure.map_apply hX (by exact MeasurableSet.of_discrete)]
  rfl

/-- The continuous-test formulation of randomized-profile convergence on the
original probability spaces, before taking any finite marginal distributions. -/
def RandomizedSequenceLike {k : ℕ} (μ : Profile.NonnegativeTimeLaw k)
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (ν : ∀ N, Measure (Ω N))
    (X : ∀ N, Ω N → RiffleUpperV2.InfiniteCuts k N) : Prop :=
  ∀ T : ℝ, 0 < T → ∀ f : Simplex k × ℝ → ℝ,
    ContinuousOn f (univ ×ˢ Icc 0 T) → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => (ν N {ω | ∃ hN : 2 ≤ N,
        |Profile.empiricalTest ((X N ω).take (horizonDepth N T)) (by omega) f -
          Profile.profileTest (Profile.extendNonnegativeProfile μ) T f| < ε}).toReal)
        atTop (𝓝 1)

end RiffleMain
