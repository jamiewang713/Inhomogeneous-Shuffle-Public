import Contracts.v1.TransferFinite
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Factorial

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

/-- Finite-sum monotonicity for the canonical real expectation. -/
theorem expect_mono (P : PMF Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    expect P f ≤ expect P g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) ENNReal.toReal_nonneg

theorem expect_nonneg (P : PMF Ω) {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ expect P f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg ENNReal.toReal_nonneg (h ω)

theorem expect_const (P : PMF Ω) (c : ℝ) : expect P (fun _ => c) = c := by
  have hsum : (∑ ω, (P ω).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun ω _ => P.apply_ne_top ω)]
    have h := P.tsum_coe
    rw [tsum_fintype] at h
    rw [h]
    simp
  simp only [expect, ← Finset.sum_mul, hsum, one_mul]

theorem expect_add (P : PMF Ω) (f g : Ω → ℝ) :
    expect P (fun ω => f ω + g ω) = expect P f + expect P g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (P : PMF Ω) (f g : Ω → ℝ) :
    expect P (fun ω => f ω - g ω) = expect P f - expect P g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_const_mul (P : PMF Ω) (c : ℝ) (f : Ω → ℝ) :
    expect P (fun ω => c * f ω) = c * expect P f := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_mul_const (P : PMF Ω) (f : Ω → ℝ) (c : ℝ) :
    expect P (fun ω => f ω * c) = expect P f * c := by
  simp [expect, mul_assoc, Finset.sum_mul]

theorem expect_div (P : PMF Ω) (f : Ω → ℝ) (c : ℝ) :
    expect P (fun ω => f ω / c) = expect P f / c := by
  simp [div_eq_mul_inv, expect_mul_const]

theorem expect_sum {ι : Type*} (P : PMF Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    expect P (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, expect P (f i) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem abs_expect_le (P : PMF Ω) (f : Ω → ℝ) :
    |expect P f| ≤ expect P (fun ω => |f ω|) := by
  unfold expect
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
    congr 1
    ext ω
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg])

theorem uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    expect (PMF.uniformOfFintype Ω) f = (∑ ω, f ω) / Fintype.card Ω := by
  simp only [expect, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← Finset.mul_sum]
  ring

theorem uniform_expect_equiv [Nonempty Ω] [Nonempty Γ] (e : Ω ≃ Γ) (f : Γ → ℝ) :
    expect (PMF.uniformOfFintype Ω) (fun ω => f (e ω)) =
      expect (PMF.uniformOfFintype Γ) f := by
  rw [uniform_expect, uniform_expect, Fintype.card_congr e, Equiv.sum_comp]

theorem uniform_pi_expect_prod {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (f : ∀ i, A i → ℝ) :
    expect (PMF.uniformOfFintype (∀ i, A i)) (fun ω => ∏ i, f i (ω i)) =
      ∏ i, expect (PMF.uniformOfFintype (A i)) (f i) := by
  simp_rw [uniform_expect]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [Fintype.card_pi, Nat.cast_prod]

theorem falling_nonneg (n r : ℕ) : 0 ≤ falling n r := Nat.cast_nonneg _

theorem choose_eq_falling_div (n r : ℕ) :
    (n.choose r : ℝ) = falling n r / r.factorial := by
  apply (eq_div_iff (by positivity : (r.factorial : ℝ) ≠ 0)).2
  unfold falling
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  ring

theorem falling_two (n : ℕ) : falling n 2 = (n : ℝ) * ((n : ℝ) - 1) :=
  Nat.cast_descFactorial_two ℝ n

theorem falling_three (n : ℕ) :
    falling n 3 = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  rcases n with _ | _ | n
  · norm_num [falling]
  · norm_num [falling]
  · simp [falling, Nat.descFactorial_succ, Nat.cast_add, Nat.cast_mul]
    ring

/-- Correct pointwise rare-category sandwich, including counts 0, 1, 2 and 3. -/
theorem rare_pointwise (n : ℕ) :
    falling n 2 / 2 - falling n 3 / 3 ≤ (if 2 ≤ n then (1 : ℝ) else 0) ∧
    (if 2 ≤ n then (1 : ℝ) else 0) ≤ falling n 2 / 2 := by
  rcases n with _ | _ | n
  · norm_num [falling]
  · norm_num [falling]
  · rw [if_pos (by omega), falling_two, falling_three]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    constructor
    · rcases n with _ | n
      · norm_num
      · push_cast
        have h := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n)
          (by positivity : 0 ≤ (n : ℝ) + 1)) (by positivity : 0 ≤ 2 * (n : ℝ) + 7)
        nlinarith
    · nlinarith

/-- The third falling-factorial coefficient is 1/3. -/
theorem rareSandwich : Targets.RareSandwich := by
  intro Ω _ P X
  constructor
  · calc
      _ = expect P (fun ω => falling (X ω) 2 / 2 - falling (X ω) 3 / 3) := by
        rw [expect_sub, expect_div, expect_div]
      _ ≤ probability P (fun ω => 2 ≤ X ω) := by
        apply expect_mono
        intro ω
        have h := (rare_pointwise (X ω)).1
        by_cases hx : 2 ≤ X ω <;> simpa [hx] using h
  · calc
      probability P (fun ω => 2 ≤ X ω) ≤ expect P (fun ω => falling (X ω) 2 / 2) := by
        apply expect_mono
        intro ω
        have h := (rare_pointwise (X ω)).2
        by_cases hx : 2 ≤ X ω <;> simpa [hx] using h
      _ = _ := expect_div P _ _

end RiffleLowerV2.Factorial
