import EdgeLocalization.FiniteLaw
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Finite-law constructors and identities in frozen collision contract C.01–C.05. -/

noncomputable section

namespace EdgeLocalization.FiniteLaw

open Finset
open scoped Classical

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := Ω))
    simp [hc]

def pi {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ j, Fintype (Ω j)] (w : ∀ j, FiniteLaw (Ω j)) :
    FiniteLaw (∀ j, Ω j) where
  weight ω := ∏ j, (w j).weight (ω j)
  nonneg ω := Finset.prod_nonneg (fun j _ => (w j).nonneg (ω j))
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp only [fun j => (w j).total, Finset.prod_const_one]

theorem uniform_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) :
    (uniform Ω).probability A =
      ((Finset.univ.filter A).card : ℝ) / (Fintype.card Ω : ℝ) := by
  classical
  unfold probability expectation uniform
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv, mul_comm]

theorem uniform_probability_reindex {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (e : Ω ≃ Ω) (A : Ω → Prop) :
    (uniform Ω).probability (fun ω => A (e ω)) = (uniform Ω).probability A := by
  classical
  unfold probability expectation uniform
  exact e.sum_comp (fun ω => (Fintype.card Ω : ℝ)⁻¹ * if A ω then 1 else 0)

theorem pi_probability {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ j, Fintype (Ω j)] (w : ∀ j, FiniteLaw (Ω j))
    (A : ∀ j, Ω j → Prop) :
    (pi w).probability (fun ω => ∀ j, A j (ω j)) =
      ∏ j, (w j).probability (A j) := by
  classical
  unfold probability expectation
  simp only [pi]
  calc
    _ = ∑ ω : ∀ j, Ω j, ∏ j,
        ((w j).weight (ω j) * if A j (ω j) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.prod_mul_distrib, Fintype.prod_boole]
      by_cases h : ∀ j, A j (ω j) <;> simp [h]
    _ = _ := (Fintype.prod_sum
      (fun j z => (w j).weight z * if A j z then 1 else 0)).symm

theorem pi_probability_on_finset {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ j, Fintype (Ω j)] (w : ∀ j, FiniteLaw (Ω j))
    (s : Finset ι) (A : ∀ j, Ω j → Prop) :
    (pi w).probability (fun ω => ∀ j ∈ s, A j (ω j)) =
      ∏ j ∈ s, (w j).probability (A j) := by
  classical
  calc
    _ = ∏ j, (w j).probability (fun z => j ∈ s → A j z) :=
      pi_probability w (fun j z => j ∈ s → A j z)
    _ = ∏ j, if j ∈ s then (w j).probability (A j) else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j ∈ s
      · simp [hj]
      · simp [hj, probability_true]
    _ = _ := by simp

theorem probability_disjoint_indexed_union {Ω : Type*} [Fintype Ω]
    (w : FiniteLaw Ω) {α : Type*} [Fintype α] (A : α → Ω → Prop)
    (hA : ∀ ω a b, A a ω → A b ω → a = b) :
    w.probability (fun ω => ∃ a, A a ω) = ∑ a, w.probability (A a) := by
  classical
  unfold probability expectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.mul_sum]
  congr 1
  dsimp only
  by_cases h : ∃ a, A a ω
  · obtain ⟨a, ha⟩ := h
    rw [if_pos ⟨a, ha⟩]
    symm
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hba
      have hb : ¬ A b ω := fun hb => hba (hA ω b a hb ha)
      simp [hb]
    · simp
  · simp only [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro a _
    simp [show ¬ A a ω from fun ha => h ⟨a, ha⟩]

end EdgeLocalization.FiniteLaw
