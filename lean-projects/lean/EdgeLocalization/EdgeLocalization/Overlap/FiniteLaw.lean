import EdgeLocalization.FiniteLaw
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

/-! Frozen independent-copy product law and intersection identities S.D01, S.01–03. -/

noncomputable section

namespace EdgeLocalization.FiniteLaw

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

def prod (w : FiniteLaw Ω) (v : FiniteLaw Λ) : FiniteLaw (Ω × Λ) where
  weight z := w.weight z.1 * v.weight z.2
  nonneg z := mul_nonneg (w.nonneg z.1) (v.nonneg z.2)
  total := by
    classical
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, v.total, mul_one, w.total]

theorem prod_expectation (w : FiniteLaw Ω) (v : FiniteLaw Λ)
    (f : Ω × Λ → ℝ) :
    (w.prod v).expectation f =
      w.expectation (fun ω => v.expectation (fun ζ => f (ω, ζ))) := by
  classical
  unfold expectation
  change (∑ z : Ω × Λ, w.weight z.1 * v.weight z.2 * f z) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ζ _
  exact mul_assoc _ _ _

theorem prod_probability (w : FiniteLaw Ω) (v : FiniteLaw Λ)
    (A : Ω → Prop) (B : Λ → Prop) :
    (w.prod v).probability (fun z => A z.1 ∧ B z.2) =
      w.probability A * v.probability B := by
  classical
  unfold probability
  rw [prod_expectation]
  unfold expectation
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ζ _
  by_cases hA : A ω <;> by_cases hB : B ζ <;>
    simp only [hA, hB, and_true, and_false,
      if_true, if_false, mul_zero, zero_mul, mul_one]

theorem expected_card_intersection (w : FiniteLaw Ω) (v : FiniteLaw Λ)
    {α : Type*} [DecidableEq α] (s : Finset α)
    (H : Ω → Finset α) (J : Λ → Finset α)
    (hH : ∀ ω, H ω ⊆ s) (hJ : ∀ ζ, J ζ ⊆ s) :
    (w.prod v).expectation (fun z => ((H z.1 ∩ J z.2).card : ℝ)) =
      ∑ i ∈ s, w.probability (fun ω => i ∈ H ω) *
        v.probability (fun ζ => i ∈ J ζ) := by
  classical
  have hsub (z : Ω × Λ) : H z.1 ∩ J z.2 ⊆ s := by
    simpa only [Finset.inter_self] using Finset.inter_subset_inter (hH z.1) (hJ z.2)
  calc
    _ = ∑ i ∈ s, (w.prod v).probability (fun z => i ∈ H z.1 ∩ J z.2) :=
      ((w.prod v).sum_probabilities_eq_expected_card s
        (fun z => H z.1 ∩ J z.2) hsub).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (w.prod v).probability (fun z => i ∈ H z.1 ∧ i ∈ J z.2) := by
          apply (w.prod v).probability_congr
          intro z
          exact Finset.mem_inter
        _ = _ := w.prod_probability v (fun ω => i ∈ H ω) (fun ζ => i ∈ J ζ)

end EdgeLocalization.FiniteLaw
