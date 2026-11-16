import RiffleLowerV2.Factorial.Basic
import RiffleLowerV2.Model.FiniteLaws

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.GraphOverlap
open RiffleLowerV2.Factorial

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expect_comm (P : PMF Ω) (Q : PMF Γ) (f : Ω → Γ → ℝ) :
    RiffleLowerV2.expect P (fun ω => RiffleLowerV2.expect Q (f ω)) =
      RiffleLowerV2.expect Q (fun γ => RiffleLowerV2.expect P (fun ω => f ω γ)) := by
  unfold RiffleLowerV2.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_product (P : PMF Ω) (Q : PMF Γ) (f : Ω → ℝ) (g : Γ → ℝ) :
    RiffleLowerV2.expect P f * RiffleLowerV2.expect Q g =
      RiffleLowerV2.expect P (fun ω => RiffleLowerV2.expect Q (fun γ => f ω * g γ)) := by
  simp only [expect_const_mul, expect_mul_const]

/-- Finite Cauchy--Schwarz, derived from positivity of the centered square. -/
theorem expect_abs_le_sqrt (P : PMF Ω) (f : Ω → ℝ) :
    RiffleLowerV2.expect P (fun ω => |f ω|) ≤
      Real.sqrt (RiffleLowerV2.expect P (fun ω => f ω ^ 2)) := by
  let m := RiffleLowerV2.expect P (fun ω => |f ω|)
  have hv := expect_nonneg P (fun ω => sq_nonneg (|f ω| - m))
  have heq : RiffleLowerV2.expect P (fun ω => (|f ω| - m)^2) =
      RiffleLowerV2.expect P (fun ω => f ω^2) - m^2 := by
    have hh : (fun ω => (|f ω| - m)^2) =
        (fun ω => f ω^2 - 2*m*|f ω| + m^2) := by
      funext ω
      nlinarith [sq_abs (f ω)]
    rw [hh, expect_add, expect_sub, expect_const_mul, expect_const]
    dsimp [m]
    ring
  rw [heq] at hv
  have hm := expect_nonneg P (fun ω => abs_nonneg (f ω))
  have hf := expect_nonneg P (fun ω => sq_nonneg (f ω))
  have hs := Real.sq_sqrt hf
  have hr := Real.sqrt_nonneg (RiffleLowerV2.expect P (fun ω => f ω^2))
  change m ≤ _
  change 0 ≤ m at hm
  nlinarith

theorem probability_compl (P : PMF Ω) (A : Ω → Prop) :
    RiffleLowerV2.probability P (fun ω => ¬ A ω) = 1 - RiffleLowerV2.probability P A := by
  calc
    _ = RiffleLowerV2.expect P (fun ω => 1 - if A ω then (1 : ℝ) else 0) := by
      unfold RiffleLowerV2.probability
      congr 1
      funext ω
      by_cases h : A ω <;> simp [h]
    _ = _ := by rw [expect_sub, expect_const]; rfl

end RiffleUpperV2.GraphOverlap
