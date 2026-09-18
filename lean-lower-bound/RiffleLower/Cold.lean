import RiffleLower.Sorting
import Mathlib.Tactic

namespace RiffleLower

open Finset

def tiltedEntropy (theta J B : ℝ) : ℝ := theta * J - B

def coldSize (beta theta J B : ℝ) : ℝ := beta - J + tiltedEntropy theta J B

def coldCollision (beta theta J J2 B B2 : ℝ) : ℝ :=
  2 * beta - 2 * J - 2 * J2 + tiltedEntropy theta J B + tiltedEntropy 2 J2 B2

noncomputable def coldMargin (beta theta B B2 : ℝ) : ℝ := (theta + 3) * beta / 2 - B - 2 * B2

def pathPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  univ.filter fun e => e.2.val = e.1.val + 1

noncomputable def equalKeyEdges {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (H : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (pathPairs N).filter fun e => e.1 ∈ H ∧ e.2 ∈ H ∧ sortedKey f e.1 = sortedKey f e.2

def ascentEdges {N : ℕ} (sigma : Equiv.Perm (Fin N)) (H : Finset (Fin N)) :
    Finset (Fin N × Fin N) :=
  (pathPairs N).filter fun e => e.1 ∈ H ∧ e.2 ∈ H ∧ sigma e.1 < sigma e.2

noncomputable def localizedKeys {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (S : Finset W) (H : Finset (Fin N)) : Prop :=
  ∀ w ∈ S, ∀ i : Fin N, sortedKey f i = w → i ∈ H

/-- C1: the exact finite cold-margin identity; no asymptotic claim is used. -/
theorem cold_exponent_identity (beta theta J J2 B B2 : ℝ) :
    2 * coldCollision beta theta J J2 B B2 - coldSize beta theta J B -
      coldMargin beta theta B B2 = (theta - 3) * (J - beta / 2) := by
  unfold coldCollision coldSize coldMargin tiltedEntropy
  ring

/-- C2: localized repeated complete keys supply distinct equal-key edges. -/
theorem localized_collisions_supply_edges {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (S : Finset W) (H : Finset (Fin N)) (hloc : localizedKeys f S H) :
    (S.filter fun w => 2 ≤ keyCount f w).card ≤ (equalKeyEdges f H).card := by
  classical
  have hrbound (w : W) : lowerRank f w + keyCount f w ≤ N := by
    have hd : Disjoint (univ.filter fun j => f j < w) (univ.filter fun j => f j = w) := by
      apply disjoint_left.mpr
      intro j hj hk
      exact (ne_of_lt (mem_filter.mp hj).2) (mem_filter.mp hk).2
    change (univ.filter fun j => f j < w).card + (univ.filter fun j => f j = w).card ≤ N
    rw [← card_union_of_disjoint hd]
    exact (card_le_card (subset_univ _)).trans_eq (card_univ.trans (Fintype.card_fin N))
  let A := S.filter fun w => 2 ≤ keyCount f w
  have htwo (w : A) : 2 ≤ keyCount f w.val := (mem_filter.mp w.property).2
  let edge : A → Fin N × Fin N := fun w =>
    (⟨lowerRank f w.val, by have := hrbound w.val; have := htwo w; omega⟩,
     ⟨lowerRank f w.val + 1, by have := hrbound w.val; have := htwo w; omega⟩)
  have hfirst (w : A) : sortedKey f (edge w).1 = w.val := by
    apply (sorted_fiber_interval f w.val (edge w).1).mpr
    change lowerRank f w.val ≤ lowerRank f w.val ∧
      lowerRank f w.val < lowerRank f w.val + keyCount f w.val
    have := htwo w
    omega
  have hsecond (w : A) : sortedKey f (edge w).2 = w.val := by
    apply (sorted_fiber_interval f w.val (edge w).2).mpr
    change lowerRank f w.val ≤ lowerRank f w.val + 1 ∧
      lowerRank f w.val + 1 < lowerRank f w.val + keyCount f w.val
    have := htwo w
    omega
  have hmem (w : A) : edge w ∈ equalKeyEdges f H := by
    have hws : w.val ∈ S := (mem_filter.mp w.property).1
    simp only [equalKeyEdges, pathPairs, mem_filter, mem_univ, true_and]
    exact ⟨rfl, hloc w.val hws (edge w).1 (hfirst w),
      hloc w.val hws (edge w).2 (hsecond w), (hfirst w).trans (hsecond w).symm⟩
  let witness : A → equalKeyEdges f H := fun w => ⟨edge w, hmem w⟩
  have hinj : Function.Injective witness := by
    intro w v he
    apply Subtype.ext
    have he' : edge w = edge v := congrArg Subtype.val he
    calc
      w.val = sortedKey f (edge w).1 := (hfirst w).symm
      _ = sortedKey f (edge v).1 := congrArg (fun e => sortedKey f e.1) he'
      _ = v.val := hfirst v
  simpa only [Fintype.card_coe, A] using Fintype.card_le_of_injective witness hinj

/-- C3a: stable sorting makes each equal-key edge an ascent. -/
theorem equalKeyEdges_subset_ascents {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (H : Finset (Fin N)) :
    equalKeyEdges f H ⊆ ascentEdges (stableSort f) H := by
  intro e he
  simp only [equalKeyEdges, pathPairs, mem_filter, mem_univ, true_and] at he
  simp only [ascentEdges, pathPairs, mem_filter, mem_univ, true_and]
  have hij : e.1 < e.2 := by change e.1.val < e.2.val; omega
  exact ⟨he.1, he.2.1, he.2.2.1, stable_tie_increasing f hij he.2.2.2⟩

/-- C3b: the corresponding finite ascent-count lower bound. -/
theorem equalKeyEdges_card_le_ascents {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (H : Finset (Fin N)) :
    (equalKeyEdges f H).card ≤ (ascentEdges (stableSort f) H).card :=
  card_le_card (equalKeyEdges_subset_ascents f H)

end RiffleLower
