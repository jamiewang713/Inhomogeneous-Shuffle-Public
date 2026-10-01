import RiffleLowerV2.Ascent.FiniteProbability
import RiffleLowerV2.Model.FiniteLaws

/-! Conditional observable tests for a graph law and an independent uniform permutation.
These identities do not identify any physical shuffle law with this mixture. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Ascent

/-- The literal independent-uniform component-sorting mixture for an arbitrary path-graph law. -/
def pathGraphMixture {N : ℕ} (ρ : PMF (PathEdges N)) : PMF (Permutation N) :=
  ρ.bind fun G => (uniformPermutation N).map (componentSort G)

theorem probability_pathGraphMixture {N : ℕ} (ρ : PMF (PathEdges N))
    (A : Permutation N → Prop) :
    probability (pathGraphMixture ρ) A = expect ρ (fun G =>
      probability (uniformPermutation N) (fun π => A (componentSort G π))) := by
  unfold probability pathGraphMixture
  rw [Model.expect_bind]
  congr 1
  funext G
  exact Model.expect_map _ _ _

/-- Uniform conditional success costs at most epsilon after averaging the graph. -/
theorem graph_mixture_event_lower {N : ℕ} (ρ : PMF (PathEdges N))
    (good : PathEdges N → Prop) (A : Permutation N → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ G, good G → 1-ε ≤
      probability (uniformPermutation N) (fun π => A (componentSort G π))) :
    probability ρ good - ε ≤ probability (pathGraphMixture ρ) A := by
  rw [probability_pathGraphMixture]
  have hpoint (G : PathEdges N) : (if good G then (1 : ℝ) else 0)-ε ≤
      probability (uniformPermutation N) (fun π => A (componentSort G π)) := by
    by_cases hg : good G
    · simpa only [if_pos hg] using hgood G hg
    · simp only [if_neg hg, zero_sub]
      exact (neg_nonpos.mpr hε).trans (probability_nonneg _ _)
  have h := expect_mono ρ hpoint
  rwa [expect_sub, expect_const] at h

/-- The shared half-L1 total variation controls every observable event difference. -/
theorem probability_sub_le_tv {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) (A : Ω → Prop) :
    probability P A - probability Q A ≤ tv P Q := by
  let d := fun ω => (P ω).toReal-(Q ω).toReal
  have hsum (R : PMF Ω) : (∑ ω, (R ω).toReal) = 1 := by
    simpa only [expect, mul_one] using expect_const R 1
  have hd : (∑ ω, d ω) = 0 := by
    dsimp [d]
    rw [Finset.sum_sub_distrib, hsum, hsum]
    ring
  have hA : (∑ ω, if A ω then d ω else 0) = probability P A-probability Q A := by
    unfold probability expect
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases ha : A ω <;> simp [ha, d]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    show 2*(if A ω then d ω else 0)-d ω ≤ |d ω| from by
      by_cases ha : A ω
      · simp only [if_pos ha]
        linarith [le_abs_self (d ω)]
      · simpa only [if_neg ha, mul_zero, zero_sub] using neg_le_abs (d ω))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hd, hA, sub_zero] at h
  change _ ≤ (∑ ω, |d ω|)/2
  linarith

/-- The shared half-L1 distance of two finite probability laws is at most one. -/
theorem tv_le_one {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) : tv P Q ≤ 1 := by
  have hsum (R : PMF Ω) : (∑ ω, (R ω).toReal) = 1 := by
    simpa only [expect, mul_one] using expect_const R 1
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    show |(P ω).toReal-(Q ω).toReal| ≤ (P ω).toReal+(Q ω).toReal from by
      apply abs_le.mpr
      constructor <;> linarith [ENNReal.toReal_nonneg (a := P ω), ENNReal.toReal_nonneg (a := Q ω)])
  rw [Finset.sum_add_distrib, hsum, hsum] at h
  unfold tv
  linarith

/-- A finite conditional Lalley test. The equality premise is visible and must be discharged. -/
theorem graph_mixture_tv_lower {N : ℕ} (ρ : PMF (PathEdges N))
    (P : PMF (Permutation N)) (hP : P = pathGraphMixture ρ)
    (good : PathEdges N → Prop) (A : Permutation N → Prop) {ε η : ℝ}
    (hε : 0 ≤ ε)
    (hgood : ∀ G, good G → 1-ε ≤
      probability (uniformPermutation N) (fun π => A (componentSort G π)))
    (huniform : probability (uniformPermutation N) A ≤ η) :
    probability ρ good-ε-η ≤ tv P (uniformPermutation N) := by
  subst P
  have hp := graph_mixture_event_lower ρ good A hε hgood
  have ht := probability_sub_le_tv (pathGraphMixture ρ) (uniformPermutation N) A
  linarith

end RiffleLowerV2.Ascent
