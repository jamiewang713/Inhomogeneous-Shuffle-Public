import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import RiffleShuffle.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Normalized finite pile profiles and word masses, contract P01–P14. -/

noncomputable section
open scoped BigOperators
namespace RiffleShuffle

namespace PileProfile

variable {N k K : ℕ} (P : PileProfile N k K)

theorem countAt_of_lt (j : ℕ) (a : Fin k) (h : j < K) :
    P.countAt j a = P.count ⟨j, h⟩ a := by
  simp [countAt, h]

theorem countAt_of_ge (j : ℕ) (a : Fin k) (h : K ≤ j) :
    P.countAt j a = 0 := by
  simp [countAt, Nat.not_lt.mpr h]

theorem count_le_deck (j : Fin K) (a : Fin k) : P.count j a ≤ N := by
  calc
    P.count j a ≤ ∑ b, P.count j b :=
      Finset.single_le_sum (fun b _ => Nat.zero_le (P.count j b)) (Finset.mem_univ a)
    _ = N := P.total j

theorem prob_nonneg (j : ℕ) (a : Fin k) : 0 ≤ P.probAt j a := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem prob_le_one (j : ℕ) (a : Fin k) : P.probAt j a ≤ 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast P.deck_pos
  by_cases h : j < K
  · rw [probAt, P.countAt_of_lt j a h]
    apply (div_le_one hN).2
    exact_mod_cast P.count_le_deck ⟨j, h⟩ a
  · simp [probAt, countAt, h]

theorem prob_pos_iff (j : ℕ) (a : Fin k) :
    0 < P.probAt j a ↔ 0 < P.countAt j a := by
  have hN : (0 : ℝ) < N := by exact_mod_cast P.deck_pos
  rw [probAt, div_pos_iff_of_pos_right hN]
  exact Nat.cast_pos

theorem prob_sum (j : ℕ) (h : j < K) : ∑ a, P.probAt j a = 1 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.deck_pos
  simp only [probAt, P.countAt_of_lt j _ h, ← Finset.sum_div]
  rw [← Nat.cast_sum, P.total, div_self hN]

theorem exists_positive_digit (j : ℕ) (h : j < K) :
    ∃ a : Fin k, 0 < P.countAt j a := by
  by_contra hnone
  push Not at hnone
  have hz : ∀ a : Fin k, P.count ⟨j, h⟩ a = 0 := by
    intro a
    have ha := hnone a
    rw [P.countAt_of_lt j a h] at ha
    exact Nat.eq_zero_of_le_zero ha
  have htotal := P.total ⟨j, h⟩
  simp only [hz, Finset.sum_const_zero] at htotal
  exact Nat.ne_of_gt P.deck_pos htotal.symm

def normalized (j : Fin K) : NormalizedProfile k :=
  ⟨fun a => P.probAt j.val a,
    ⟨fun a => ⟨P.prob_nonneg j.val a, P.prob_le_one j.val a⟩,
      P.prob_sum j.val j.isLt⟩⟩

end PileProfile

variable {N k K m : ℕ} (P : PileProfile N k K)

theorem mass_empty : mass P (emptyWord k) = 1 := by
  simp [mass]

theorem mass_nonneg (x : Word k m) : 0 ≤ mass P x := by
  exact Finset.prod_nonneg (fun j _ => P.prob_nonneg j.val (x.get j))

theorem mass_le_one (x : Word k m) : mass P x ≤ 1 := by
  exact Finset.prod_le_one
    (fun j _ => P.prob_nonneg j.val (x.get j))
    (fun j _ => P.prob_le_one j.val (x.get j))

theorem mass_pos_iff_legal (x : Word k m) (hm : m ≤ K) :
    0 < mass P x ↔ Legal P x := by
  constructor
  · intro hx
    refine ⟨hm, fun j => ?_⟩
    apply (P.prob_pos_iff j.val (x.get j)).1
    have hne : P.probAt j.val (x.get j) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp (ne_of_gt hx)) j (Finset.mem_univ j)
    exact lt_of_le_of_ne (P.prob_nonneg j.val (x.get j)) hne.symm
  · intro hx
    exact Finset.prod_pos (fun j _ => (P.prob_pos_iff j.val (x.get j)).2 (hx.2 j))

theorem mass_sum (hm : m ≤ K) : ∑ x : Word k m, mass P x = 1 := by
  classical
  calc
    ∑ x : Word k m, mass P x =
        ∑ f : Fin m → Fin k, ∏ j : Fin m, P.probAt j.val (f j) :=
      Fintype.sum_equiv (Equiv.vectorEquivFin (Fin k) m) _ _ (fun _ => rfl)
    _ = ∏ j : Fin m, ∑ a : Fin k, P.probAt j.val a :=
      (Fintype.prod_sum (fun j : Fin m => fun a : Fin k => P.probAt j.val a)).symm
    _ = ∏ _j : Fin m, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro j _
      exact P.prob_sum j.val (lt_of_lt_of_le j.isLt hm)
    _ = 1 := by simp

theorem mass_append (x : Word k m) (a : Fin k) :
    mass P (appendDigit x a) = mass P x * P.probAt m a := by
  have hget : ∀ j : Fin m, (appendDigit x a).get j.castSucc = x.get j := by
    intro j
    simp [appendDigit, List.Vector.get, List.Vector.toList,
      List.get_eq_getElem, Fin.cast, j.isLt, x.2]
  have hlast : (appendDigit x a).get (Fin.last m) = a := by
    simp [appendDigit, List.Vector.get, List.Vector.toList,
      List.get_eq_getElem, Fin.cast, x.2]
  unfold mass
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, hget, Fin.val_last, hlast]

end RiffleShuffle
