import Mathlib.Tactic

/-! Exact finite probability calculus, frozen statements F01–F13.
No concentration or shuffle estimate is part of the law's definition. -/

noncomputable section

namespace EdgeLocalization

open Finset

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def expectation (w : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, w.weight ω * f ω

def probability (w : FiniteLaw Ω) (A : Ω → Prop) : ℝ := by
  classical
  exact w.expectation (fun ω => if A ω then 1 else 0)

theorem expectation_nonneg (w : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ w.expectation f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (w.nonneg ω) (hf ω))

theorem expectation_mono (w : FiniteLaw Ω) (f g : Ω → ℝ)
    (h : ∀ ω, f ω ≤ g ω) : w.expectation f ≤ w.expectation g := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (w.nonneg ω))

theorem expectation_const (w : FiniteLaw Ω) (c : ℝ) :
    w.expectation (fun _ => c) = c := by
  simp only [expectation, ← Finset.sum_mul, w.total, one_mul]

theorem probability_nonneg (w : FiniteLaw Ω) (A : Ω → Prop) :
    0 ≤ w.probability A := by
  classical
  apply w.expectation_nonneg
  intro ω
  split_ifs <;> norm_num

theorem probability_le_one (w : FiniteLaw Ω) (A : Ω → Prop) :
    w.probability A ≤ 1 := by
  classical
  calc
    w.probability A ≤ w.expectation (fun _ => 1) := by
      apply w.expectation_mono
      intro ω
      split_ifs <;> norm_num
    _ = 1 := w.expectation_const 1

theorem probability_true (w : FiniteLaw Ω) :
    w.probability (fun _ => True) = 1 := by
  simp only [probability, if_true]
  exact w.expectation_const 1

theorem probability_false (w : FiniteLaw Ω) :
    w.probability (fun _ => False) = 0 := by
  simp only [probability, if_false]
  exact w.expectation_const 0

theorem probability_congr (w : FiniteLaw Ω) (A B : Ω → Prop)
    (h : ∀ ω, A ω ↔ B ω) : w.probability A = w.probability B := by
  classical
  unfold probability expectation
  apply Finset.sum_congr rfl
  intro ω _
  simp only [h ω]

theorem probability_sq_le (w : FiniteLaw Ω) (A : Ω → Prop) :
    (w.probability A) ^ 2 ≤ w.probability A := by
  have h := mul_le_mul_of_nonneg_left (w.probability_le_one A)
    (w.probability_nonneg A)
  nlinarith

theorem probability_of_forall (w : FiniteLaw Ω) (A : Ω → Prop)
    (h : ∀ ω, A ω) : w.probability A = 1 := by
  calc
    w.probability A = w.probability (fun _ => True) :=
      w.probability_congr _ _ (fun ω => iff_true_intro (h ω))
    _ = 1 := w.probability_true

theorem probability_event_of_constant (w : FiniteLaw Ω)
    {α : Type*} [DecidableEq α] (X : Ω → α) (j : α) (A : Ω → Prop)
    (h : ∀ ω, X ω = j) :
    w.probability (fun ω => X ω = j ∧ A ω) = w.probability A := by
  apply w.probability_congr
  intro ω
  simp only [h ω, true_and]

theorem sum_probabilities_eq_expected_card (w : FiniteLaw Ω)
    {α : Type*} [DecidableEq α] (s : Finset α) (H : Ω → Finset α)
    (hH : ∀ ω, H ω ⊆ s) :
    ∑ i ∈ s, w.probability (fun ω => i ∈ H ω) =
      w.expectation (fun ω => (H ω).card) := by
  classical
  unfold probability expectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.mul_sum]
  have hfilter : s.filter (fun i => i ∈ H ω) = H ω := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun hi => ⟨hH ω hi, hi⟩⟩
  have hsum : ∑ i ∈ s, (if i ∈ H ω then (1 : ℝ) else 0) = (H ω).card := by
    rw [← Finset.sum_filter, hfilter]
    simp
  apply congrArg (fun z : ℝ => w.weight ω * z)
  calc
    _ = ∑ i ∈ s, (if i ∈ H ω then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ H ω <;> simp [hi]
    _ = _ := hsum

theorem sum_sq_probabilities_le_expected_card (w : FiniteLaw Ω)
    {α : Type*} [DecidableEq α] (s : Finset α) (H : Ω → Finset α)
    (hH : ∀ ω, H ω ⊆ s) :
    ∑ i ∈ s, (w.probability (fun ω => i ∈ H ω)) ^ 2 ≤
      w.expectation (fun ω => (H ω).card) := by
  calc
    _ ≤ ∑ i ∈ s, w.probability (fun ω => i ∈ H ω) :=
      Finset.sum_le_sum (fun i _ => w.probability_sq_le (fun ω => i ∈ H ω))
    _ = _ := w.sum_probabilities_eq_expected_card s H hH

end FiniteLaw
end EdgeLocalization
