import RiffleLowerV2.Shared.Adapters
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Fintype

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Thinning

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expect_mono (P : PMF Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    expect P f ≤ expect P g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) ENNReal.toReal_nonneg

theorem expect_nonneg (P : PMF Ω) {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ expect P f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg ENNReal.toReal_nonneg (h ω)

theorem expect_const_mul (P : PMF Ω) (c : ℝ) (f : Ω → ℝ) :
    expect P (fun ω => c * f ω) = c * expect P f := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_add (P : PMF Ω) (f g : Ω → ℝ) :
    expect P (fun ω => f ω + g ω) = expect P f + expect P g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem probability_mono (P : PMF Ω) {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) :
    probability P A ≤ probability P B := by
  apply expect_mono
  intro ω
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp_all

theorem probability_nonneg (P : PMF Ω) (A : Ω → Prop) : 0 ≤ probability P A := by
  apply expect_nonneg
  intro ω
  split_ifs <;> norm_num

theorem probability_union_le (P : PMF Ω) (A B : Ω → Prop) :
    probability P (fun ω => A ω ∨ B ω) ≤ probability P A + probability P B := by
  simp only [probability]
  rw [← expect_add]
  apply expect_mono
  intro ω
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha, hb]

theorem probability_iUnion_le {I : Type*} [Fintype I] (P : PMF Ω) (A : I → Ω → Prop) :
    probability P (fun ω => ∃ i, A i ω) ≤ ∑ i, probability P (A i) := by
  simp only [probability, expect]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  by_cases ha : ∃ i, A i ω
  · obtain ⟨i, hi⟩ := ha
    simp only [show (∃ i, A i ω) by exact ⟨i, hi⟩, if_true]
    exact le_trans (by simp [hi]) (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i))
  · simp only [ha, if_false]
    exact Finset.sum_nonneg fun _ _ => by positivity

theorem markov (P : PMF Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    {t : ℝ} (ht : 0 < t) : probability P (fun ω => t ≤ f ω) ≤ expect P f / t := by
  apply (le_div_iff₀ ht).2
  rw [mul_comm, probability, ← expect_const_mul]
  apply expect_mono
  intro ω
  by_cases h : t ≤ f ω <;> simp [h, hf ω]

theorem uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    expect (PMF.uniformOfFintype Ω) f = (∑ ω, f ω) / Fintype.card Ω := by
  simp only [expect, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← Finset.mul_sum]
  ring

theorem uniform_expect_equiv [Nonempty Ω] [Nonempty Γ] (e : Ω ≃ Γ) (f : Γ → ℝ) :
    expect (PMF.uniformOfFintype Ω) (fun ω => f (e ω)) =
      expect (PMF.uniformOfFintype Γ) f := by
  rw [uniform_expect, uniform_expect, Fintype.card_congr e, Equiv.sum_comp]

theorem uniform_probability [Nonempty Ω] (A : Ω → Prop) :
    probability (PMF.uniformOfFintype Ω) A =
      (Fintype.card {ω // A ω} : ℝ) / Fintype.card Ω := by
  rw [probability, uniform_expect]
  congr 1
  rw [Fintype.card_subtype, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Equal finite fibres give the exact uniform pushforward expectation. -/
theorem uniform_expect_of_equal_fibres [Nonempty Ω] [Nonempty Γ] (f : Ω → Γ)
    (hf : ∀ b c : Γ, Fintype.card {ω // f ω = b} = Fintype.card {ω // f ω = c})
    (g : Γ → ℝ) :
    expect (PMF.uniformOfFintype Ω) (fun ω => g (f ω)) =
      expect (PMF.uniformOfFintype Γ) g := by
  let b : Γ := Classical.choice inferInstance
  have hc : Fintype.card Ω = Fintype.card Γ * Fintype.card {ω // f ω = b} := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
    simp_rw [hf _ b]
    simp
  have hd : (Fintype.card {ω // f ω = b} : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card {ω // f ω = b} := by
      have := Fintype.card_pos (α := Ω)
      rw [hc] at this
      exact Nat.pos_of_ne_zero (by intro hz; simp [hz] at this)
    exact_mod_cast hpos.ne'
  rw [uniform_expect, uniform_expect]
  have hs : (∑ ω, g (f ω)) = ∑ c : Γ, (Fintype.card {ω // f ω = c} : ℝ) * g c := by
    rw [← Equiv.sum_comp (Equiv.sigmaFiberEquiv f), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    change (∑ y : {ω // f ω = c}, g (f y.val)) = _
    simp_rw [show ∀ y : {ω // f ω = c}, f y.val = c from fun y => y.property]
    simp
  rw [hs, hc, Nat.cast_mul]
  simp_rw [hf _ b]
  rw [← Finset.mul_sum]
  field_simp

theorem uniform_expect_const [Nonempty Ω] (c : ℝ) :
    expect (PMF.uniformOfFintype Ω) (fun _ => c) = c := by
  rw [uniform_expect]
  simp [Fintype.card_ne_zero]

theorem uniform_product_expect [Nonempty Ω] [Nonempty Γ] (f : Ω × Γ → ℝ) :
    expect (PMF.uniformOfFintype (Ω × Γ)) f =
      expect (PMF.uniformOfFintype Ω) (fun a =>
        expect (PMF.uniformOfFintype Γ) (fun b => f (a,b))) := by
  simp only [uniform_expect, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.sum_div, div_div]
  rw [mul_comm (Fintype.card Ω : ℝ)]

end RiffleLowerV2.Thinning
