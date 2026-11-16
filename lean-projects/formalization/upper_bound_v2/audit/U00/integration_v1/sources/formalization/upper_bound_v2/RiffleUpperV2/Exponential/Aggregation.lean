import RiffleUpperV2.Exponential.Excess
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exponential
open RiffleLowerV2.Thinning

/-- Jensen aggregation. The finitely many explorations need no independence. -/
theorem convexExcess {d : ℕ} (hd : 0 < d) {b : ℝ} (hb : 0 < b) (x : Fin d → ℕ) :
    b^(∑ a, x a) - 1 ≤
      (∑ a, (Real.exp ((d : ℝ) * Real.log b * (x a : ℝ)) - 1)) / d := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw : (∑ _a : Fin d, (1 / (d : ℝ))) = 1 := by simp [hd0]
  have hj := convexOn_exp.map_sum_le (t := (Finset.univ : Finset (Fin d)))
    (w := fun _ => 1 / (d : ℝ))
    (p := fun a => (d : ℝ) * Real.log b * (x a : ℝ))
    (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  have hl : (∑ a : Fin d, (1 / (d : ℝ)) • ((d : ℝ) * Real.log b * (x a : ℝ))) =
      (∑ a, (x a : ℝ)) * Real.log b := by
    simp only [smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    field_simp
  rw [hl, ← Nat.cast_sum, Real.exp_nat_mul, Real.exp_log hb] at hj
  have hr : (∑ a : Fin d, (1 / (d : ℝ)) •
      Real.exp ((d : ℝ) * Real.log b * (x a : ℝ))) - 1 =
      (∑ a, (Real.exp ((d : ℝ) * Real.log b * (x a : ℝ)) - 1)) / d := by
    simp only [smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← Finset.mul_sum]
    field_simp
  exact (sub_le_sub_right hj 1).trans_eq hr

variable {Ω : Type*} [Fintype Ω]

/-- Finite adapted exploration excess for an arbitrary common final event.
The history types and terminal lengths are allowed to differ across explorations. -/
theorem finiteExplorationExcess (P : PMF Ω) (d : ℕ) (hd : 0 < d)
    (H : Fin d → Type*) [∀ a, Fintype (H a)]
    (h : ∀ a, ℕ → Ω → H a) (X : Fin d → ℕ → Ω → ℕ)
    (B : Fin d → ℕ → Ω → Prop) (m : Fin d → ℕ)
    (γ b : ℝ) (hγ : 0 ≤ γ) (hb : 1 ≤ b)
    (href : ∀ a, Refining (h a) (m a))
    (hunit : ∀ a ω, UnitIncrements (fun i => X a i ω) (m a))
    (hzero : ∀ a ω, X a 0 ω = 0)
    (had : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (X a i))
    (hB : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (B a i))
    (htail : ∀ a i, i < m a → ∀ v, B a i v →
      0 < probability P (fun ω => h a i ω = h a i v) →
      conditionalExpect P (fun ω => (X a (m a) ω - X a i ω : ℕ))
        (fun ω => h a i ω = h a i v) ≤ γ)
    (C : Ω → Prop) (hC : ∀ ω, C ω → ∀ a, goodPrefix (B a) (m a) ω)
    (Y : Ω → ℕ) (hcover : ∀ ω, C ω → Y ω ≤ ∑ a, X a (m a) ω)
    (hqγ : (b^d - 1)*γ < 1) :
    expect P (fun ω => if C ω then b^(Y ω) - 1 else 0) ≤
      (b^d - 1)*γ / (1-(b^d - 1)*γ) := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have ht : 0 ≤ (d : ℝ) * Real.log b := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hb)
  have hq : Real.exp ((d : ℝ) * Real.log b) - 1 = b^d - 1 := by
    rw [Real.exp_nat_mul, Real.exp_log hbpos]
  have heach (a : Fin d) : expect P (fun ω => if C ω then
      Real.exp (((d : ℝ) * Real.log b) * (X a (m a) ω : ℝ)) - 1 else 0) ≤
      (b^d - 1)*γ / (1-(b^d - 1)*γ) := by
    have he := adaptedExcess P (h a) (X a) (B a) (m a) γ hγ (href a)
      (hunit a) (hzero a) (had a) (hB a) (htail a) C (fun ω hω => hC ω hω a)
      ((d : ℝ) * Real.log b) ht (by simpa only [hq] using hqγ)
    simpa only [hq] using he
  have hpoint (ω : Ω) : (if C ω then b^(Y ω)-1 else 0) ≤
      (∑ a, if C ω then Real.exp ((d : ℝ) * Real.log b * (X a (m a) ω : ℝ))-1 else 0) / d := by
    by_cases hc : C ω
    · simp only [hc, if_true]
      calc
        b^(Y ω)-1 ≤ b^(∑ a, X a (m a) ω)-1 :=
          sub_le_sub_right (pow_le_pow_right₀ hb (hcover ω hc)) 1
        _ ≤ _ := convexExcess hd hbpos (fun a => X a (m a) ω)
    · simp [hc]
  apply le_trans (expect_mono P hpoint)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have he : expect P (fun ω => (∑ a, if C ω then
      Real.exp ((d : ℝ) * Real.log b * (X a (m a) ω : ℝ))-1 else 0) / d) =
      (∑ a, expect P (fun ω => if C ω then
        Real.exp ((d : ℝ) * Real.log b * (X a (m a) ω : ℝ))-1 else 0)) / d := by
    simp only [expect, RiffleLowerV2.expect, mul_div_assoc, Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
  change RiffleLowerV2.expect P _ = _ at he
  rw [he]
  apply (div_le_iff₀ hdpos).mpr
  calc
    _ ≤ ∑ _a : Fin d, (b^d - 1)*γ / (1-(b^d - 1)*γ) :=
      Finset.sum_le_sum (fun a _ => heach a)
    _ = _ := by simp [mul_comm]

end RiffleUpperV2.Exponential
