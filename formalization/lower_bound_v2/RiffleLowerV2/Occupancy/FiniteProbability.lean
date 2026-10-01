import RiffleLowerV2.Factorial.Basic

/-! Finite probability identities on the frozen canonical PMF definitions.
The variance and Chebyshev arguments adapt the elementary proof patterns in
`lean-lower-bound/RiffleLower/FiniteProbability.lean`; the legacy law type and
cache are not imported. Provenance is recorded in audit/LB08/probability_provenance_v1.json. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Occupancy

open Factorial
variable {Ω : Type*} [Fintype Ω]

theorem probability_congr (P : PMF Ω) {A B : Ω → Prop}
    (h : ∀ ω, A ω ↔ B ω) : probability P A = probability P B := by
  simp only [probability]
  congr 1
  funext ω
  simp only [h ω]

theorem probability_mono (P : PMF Ω) {A B : Ω → Prop}
    (h : ∀ ω, A ω → B ω) : probability P A ≤ probability P B := by
  apply expect_mono
  intro ω
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp_all

theorem probability_nonneg (P : PMF Ω) (A : Ω → Prop) : 0 ≤ probability P A := by
  apply expect_nonneg
  intro ω
  split_ifs <;> norm_num

theorem probability_le_one (P : PMF Ω) (A : Ω → Prop) : probability P A ≤ 1 := by
  rw [← expect_const P 1]
  apply expect_mono
  intro ω
  split_ifs <;> norm_num

theorem probability_true (P : PMF Ω) : probability P (fun _ => True) = 1 := by
  simpa only [probability, if_true] using expect_const P 1

theorem probability_false (P : PMF Ω) : probability P (fun _ => False) = 0 := by
  simpa only [probability, if_false] using expect_const P 0

theorem probability_not (P : PMF Ω) (A : Ω → Prop) :
    probability P (fun ω => ¬ A ω) = 1 - probability P A := by
  calc
    _ = expect P (fun ω => 1 - (if A ω then (1 : ℝ) else 0)) := by
      apply congrArg (expect P)
      funext ω
      by_cases h : A ω <;> simp [h]
    _ = _ := by rw [expect_sub, expect_const]; rfl

theorem probability_and_le_left (P : PMF Ω) (A B : Ω → Prop) :
    probability P (fun ω => A ω ∧ B ω) ≤ probability P A :=
  probability_mono P (fun _ h => h.1)

theorem probability_and_le_right (P : PMF Ω) (A B : Ω → Prop) :
    probability P (fun ω => A ω ∧ B ω) ≤ probability P B :=
  probability_mono P (fun _ h => h.2)

theorem expect_indicator_mul (P : PMF Ω) (A B : Ω → Prop) :
    expect P (fun ω => (if A ω then (1 : ℝ) else 0) *
      (if B ω then (1 : ℝ) else 0)) = probability P (fun ω => A ω ∧ B ω) := by
  apply congrArg (expect P)
  funext ω
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha, hb]

theorem variance_eq (P : PMF Ω) (f : Ω → ℝ) :
    variance P f = expect P (fun ω => f ω ^ 2) - (expect P f)^2 := by
  have hf : (fun ω => (f ω - expect P f)^2) =
      (fun ω => (f ω^2 - (2 * expect P f) * f ω) + (expect P f)^2) := by
    funext ω
    ring
  rw [variance, hf, expect_add, expect_sub, expect_const_mul, expect_const]
  ring

theorem variance_nonneg (P : PMF Ω) (f : Ω → ℝ) : 0 ≤ variance P f :=
  expect_nonneg P (fun _ => sq_nonneg _)

theorem chebyshev (P : PMF Ω) (f : Ω → ℝ) (t : ℝ) (ht : 0 < t) :
    probability P (fun ω => t ≤ |f ω - expect P f|) ≤ variance P f / t^2 := by
  have hpoint : ∀ ω, t^2 * (if t ≤ |f ω - expect P f| then (1 : ℝ) else 0) ≤
      (f ω - expect P f)^2 := by
    intro ω
    by_cases h : t ≤ |f ω - expect P f|
    · rw [if_pos h, mul_one]
      simpa only [sq_abs] using pow_le_pow_left₀ ht.le h 2
    · rw [if_neg h, mul_zero]
      exact sq_nonneg _
  have h := expect_mono P hpoint
  rw [expect_const_mul] at h
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  simpa only [probability, variance, mul_comm] using h

/-- The finite Chebyshev consequence of the variance bound; its premise is
explicit and this is not the actual-model occupancy theorem. -/
theorem chebyshev_of_variance_le (P : PMF Ω) (f : Ω → ℝ) (η t : ℝ)
    (hμ : 0 < expect P f) (ht : 0 < t)
    (hv : variance P f ≤ expect P f + η * (expect P f)^2) :
    probability P (fun ω => t * expect P f ≤ |f ω - expect P f|) ≤
      1 / (t^2 * expect P f) + η / t^2 := by
  calc
    _ ≤ variance P f / (t * expect P f)^2 := chebyshev P f _ (mul_pos ht hμ)
    _ ≤ (expect P f + η * (expect P f)^2) / (t * expect P f)^2 :=
      div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ = _ := by field_simp

/-- Explicit success probability, with no dependence on a family cardinality. -/
theorem lower_tail_success (P : PMF Ω) (f : Ω → ℝ) (η t : ℝ)
    (hμ : 0 < expect P f) (ht : 0 < t)
    (hv : variance P f ≤ expect P f + η * (expect P f)^2) :
    1 - 1 / (t^2 * expect P f) - η / t^2 ≤
      probability P (fun ω => (1-t) * expect P f < f ω) := by
  have hs : probability P (fun ω => ¬ ((1-t) * expect P f < f ω)) ≤
      probability P (fun ω => t * expect P f ≤ |f ω - expect P f|) := by
    apply probability_mono
    intro ω h
    have hle : f ω ≤ (1-t) * expect P f := le_of_not_gt h
    have habs := neg_le_abs (f ω - expect P f)
    nlinarith
  have hb := hs.trans (chebyshev_of_variance_le P f η t hμ ht hv)
  rw [probability_not] at hb
  linarith

theorem positive_success (P : PMF Ω) (f : Ω → ℝ) (η : ℝ)
    (hμ : 0 < expect P f)
    (hv : variance P f ≤ expect P f + η * (expect P f)^2) :
    1 - 1 / expect P f - η ≤ probability P (fun ω => 0 < f ω) := by
  simpa using lower_tail_success P f η 1 hμ zero_lt_one hv

end RiffleLowerV2.Occupancy
