/- LB02 source compatibility port of `lean/Shuffle/FiniteLaw.lean`.
Original SHA-256: f5dcbcfa6908503696d6edaa363a8a0919a22aabd8e01e9819e6f13d20baff17.
Original files and freeze records are unchanged. -/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Finite probability, with the mathematical contract frozen before implementation. -/

noncomputable section
open scoped BigOperators

namespace RiffleLowerV2.Thinning.Compat

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  mass_sum : ∑ ω, mass ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (p : FiniteLaw Ω)

def prob (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then p.mass ω else 0

def expect (f : Ω → ℝ) : ℝ := ∑ ω, p.mass ω * f ω

def variance (f : Ω → ℝ) : ℝ := p.expect fun ω => (f ω - p.expect f) ^ 2

theorem prob_nonneg (E : Ω → Prop) : 0 ≤ p.prob E := by
  classical
  unfold prob
  exact Finset.sum_nonneg fun ω _ => by
    split_ifs
    · exact p.mass_nonneg ω
    · exact le_rfl

@[simp] theorem prob_true : p.prob (fun _ => True) = 1 := by
  simp [prob, p.mass_sum]

@[simp] theorem prob_false : p.prob (fun _ => False) = 0 := by
  simp [prob]

theorem prob_mono {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    p.prob E ≤ p.prob F := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω
  · simp [he, h ω he]
  · simp only [he, ↓reduceIte]
    split_ifs
    · exact p.mass_nonneg ω
    · exact le_rfl

theorem prob_le_one (E : Ω → Prop) : p.prob E ≤ 1 := by
  simpa using p.prob_mono (E := E) (F := fun _ => True) (by tauto)

theorem prob_union_le (E F : Ω → Prop) :
    p.prob (fun ω => E ω ∨ F ω) ≤ p.prob E + p.prob F := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω <;> by_cases hf : F ω <;>
    simp [he, hf, p.mass_nonneg ω]

theorem expect_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ p.expect f := by
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (p.mass_nonneg ω) (h ω)

theorem expect_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    p.expect f ≤ p.expect g := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (p.mass_nonneg ω)

@[simp] theorem expect_const (c : ℝ) : p.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, p.mass_sum]

theorem expect_add (f g : Ω → ℝ) :
    p.expect (fun ω => f ω + g ω) = p.expect f + p.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (f g : Ω → ℝ) :
    p.expect (fun ω => f ω - g ω) = p.expect f - p.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (f : Ω → ℝ) (c : ℝ) :
    p.expect (fun ω => f ω * c) = p.expect f * c := by
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_const_mul (c : ℝ) (f : Ω → ℝ) :
    p.expect (fun ω => c * f ω) = c * p.expect f := by
  simpa [mul_comm] using p.expect_mul_const f c

theorem variance_nonneg (f : Ω → ℝ) : 0 ≤ p.variance f := by
  exact p.expect_nonneg fun _ => sq_nonneg _

theorem variance_eq (f : Ω → ℝ) :
    p.variance f = p.expect (fun ω => f ω ^ 2) - p.expect f ^ 2 := by
  unfold variance
  have h : (fun ω => (f ω - p.expect f) ^ 2) =
      (fun ω => f ω ^ 2 - 2 * p.expect f * f ω + p.expect f ^ 2) := by
    funext ω
    ring
  rw [h, p.expect_add, p.expect_sub, p.expect_const_mul, p.expect_const]
  ring

theorem markov {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    p.prob (fun ω => t ≤ f ω) ≤ p.expect f / t := by
  classical
  apply (le_div_iff₀ ht).2
  unfold prob expect
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : t ≤ f ω
  · simp only [h, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left h (p.mass_nonneg ω)
  · simp only [h, ↓reduceIte, zero_mul]
    exact mul_nonneg (p.mass_nonneg ω) (hf ω)

theorem chebyshev (f : Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    p.prob (fun ω => t ≤ |f ω - p.expect f|) ≤ p.variance f / t ^ 2 := by
  have h := p.markov (fun ω => sq_nonneg (f ω - p.expect f)) (sq_pos_of_pos ht)
  calc
    p.prob (fun ω => t ≤ |f ω - p.expect f|) ≤
        p.prob (fun ω => t ^ 2 ≤ (f ω - p.expect f) ^ 2) := by
      apply p.prob_mono
      intro ω hω
      nlinarith [sq_abs (f ω - p.expect f), abs_nonneg (f ω - p.expect f)]
    _ ≤ p.variance f / t ^ 2 := h

def toPMF : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (p.mass ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => p.mass_nonneg ω), p.mass_sum]
    simp)

@[simp] theorem toPMF_apply (ω : Ω) : p.toPMF ω = ENNReal.ofReal (p.mass ω) := rfl

@[simp] theorem toPMF_toReal (ω : Ω) : (p.toPMF ω).toReal = p.mass ω :=
  ENNReal.toReal_ofReal (p.mass_nonneg ω)

theorem integral_toPMF [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (f : Ω → ℝ) :
    (∫ ω, f ω ∂p.toPMF.toMeasure) = p.expect f := by
  rw [PMF.integral_eq_sum]
  simp only [toPMF_toReal, smul_eq_mul, expect]


end FiniteLaw
end RiffleLowerV2.Thinning.Compat
