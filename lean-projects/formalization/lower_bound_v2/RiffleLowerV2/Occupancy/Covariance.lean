import RiffleLowerV2.Occupancy.FiniteProbability

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Occupancy

open Factorial
variable {Ω ι : Type*} [Fintype Ω]

def eventCount (W : Finset ι) (A : ι → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i ∈ W, if A i ω then 1 else 0

omit [Fintype Ω] in
theorem eventCount_nonneg (W : Finset ι) (A : ι → Ω → Prop) (ω : Ω) :
    0 ≤ eventCount W A ω := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> norm_num

theorem expect_eventCount (P : PMF Ω) (W : Finset ι) (A : ι → Ω → Prop) :
    expect P (eventCount W A) = ∑ i ∈ W, probability P (A i) := by
  exact expect_sum P W (fun i ω => if A i ω then 1 else 0)

theorem expect_eventCount_sq (P : PMF Ω) (W : Finset ι) (A : ι → Ω → Prop) :
    expect P (fun ω => (eventCount W A ω)^2) =
      ∑ i ∈ W, ∑ j ∈ W, probability P (fun ω => A i ω ∧ A j ω) := by
  simp only [eventCount, pow_two, Finset.sum_mul_sum, expect_sum, expect_indicator_mul]

/-- Full ordered covariance sum, including the diagonal. -/
theorem variance_eventCount (P : PMF Ω) (W : Finset ι) (A : ι → Ω → Prop) :
    variance P (eventCount W A) =
      ∑ i ∈ W, ∑ j ∈ W, (probability P (fun ω => A i ω ∧ A j ω) -
        probability P (A i) * probability P (A j)) := by
  rw [variance_eq, expect_eventCount_sq, expect_eventCount, pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_sub_distrib]

/-- Pair-relative covariance control sums without any cardinality loss. -/
theorem variance_eventCount_le (P : PMF Ω) (W : Finset ι) (A : ι → Ω → Prop)
    (η : ℝ) (hη : 0 ≤ η)
    (hpair : ∀ i ∈ W, ∀ j ∈ W, i ≠ j →
      |probability P (fun ω => A i ω ∧ A j ω) -
        probability P (A i) * probability P (A j)| ≤
        η * probability P (A i) * probability P (A j)) :
    variance P (eventCount W A) ≤ expect P (eventCount W A) +
      η * (expect P (eventCount W A))^2 := by
  classical
  have hterm (i : ι) (hi : i ∈ W) (j : ι) (hj : j ∈ W) :
      probability P (fun ω => A i ω ∧ A j ω) - probability P (A i) * probability P (A j) ≤
        (if i = j then probability P (A i) else 0) +
          η * probability P (A i) * probability P (A j) := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, probability_congr P (fun _ => and_self_iff)]
      have hp := probability_nonneg P (A i)
      have hprod := mul_nonneg (mul_nonneg hη hp) hp
      nlinarith [sq_nonneg (probability P (A i))]
    · rw [if_neg hij, zero_add]
      exact (le_abs_self _).trans (hpair i hi j hj hij)
  calc
    _ = ∑ i ∈ W, ∑ j ∈ W, (probability P (fun ω => A i ω ∧ A j ω) -
        probability P (A i) * probability P (A j)) := variance_eventCount P W A
    _ ≤ ∑ i ∈ W, ∑ j ∈ W, ((if i = j then probability P (A i) else 0) +
        η * probability P (A i) * probability P (A j)) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hterm i hi j hj))
    _ = _ := by
      simp only [Finset.sum_add_distrib, expect_eventCount]
      have hd : (∑ i ∈ W, ∑ j ∈ W, if i = j then probability P (A i) else 0) =
          ∑ i ∈ W, probability P (A i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [hi]
      rw [hd]
      congr 1
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem variance_collisionCount_le {k N K : ℕ} (cuts : TimeProfile.Cuts k N K)
    (W : Finset (Word k K)) (η : ℝ) (hη : 0 ≤ η)
    (hpair : ∀ w ∈ W, ∀ v ∈ W, w ≠ v →
      |probability (TimeProfile.fixedCountPMF cuts)
          (fun ω => collisionEvent w ω ∧ collisionEvent v ω) -
        probability (TimeProfile.fixedCountPMF cuts) (collisionEvent w) *
          probability (TimeProfile.fixedCountPMF cuts) (collisionEvent v)| ≤
        η * probability (TimeProfile.fixedCountPMF cuts) (collisionEvent w) *
          probability (TimeProfile.fixedCountPMF cuts) (collisionEvent v)) :
    variance (TimeProfile.fixedCountPMF cuts) (collisionCount W) ≤
      expect (TimeProfile.fixedCountPMF cuts) (collisionCount W) +
        η * (expect (TimeProfile.fixedCountPMF cuts) (collisionCount W))^2 :=
  variance_eventCount_le (TimeProfile.fixedCountPMF cuts) W collisionEvent η hη hpair

end RiffleLowerV2.Occupancy
