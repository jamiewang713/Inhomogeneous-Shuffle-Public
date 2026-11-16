import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

namespace RiffleLower

open Finset

noncomputable abbrev stableSort {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) : Equiv.Perm (Fin N) := Tuple.sort f

noncomputable def sortedKey {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (i : Fin N) : W := f (stableSort f i)

def keyCount {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (w : W) : ℕ := (univ.filter fun i => f i = w).card

def lowerRank {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (w : W) : ℕ := (univ.filter fun i => f i < w).card

def HasIncreasingRun {N : ℕ} (σ : Equiv.Perm (Fin N)) (m : ℕ) : Prop :=
  ∃ a : ℕ, a + m ≤ N ∧
    ∀ i j : Fin N, a ≤ i.val → j.val < a + m → i < j → σ i < σ j

/-- S1: an equal-key fiber is an interval in sorted position order. -/
theorem sorted_equal_convex {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) {i j l : Fin N} (hij : i ≤ j) (hjl : j ≤ l)
    (heq : sortedKey f i = sortedKey f l) : sortedKey f j = sortedKey f i := by
  have hm : Monotone (sortedKey f) := Tuple.monotone_sort f
  exact le_antisymm ((hm hjl).trans_eq heq.symm) (hm hij)

/-- S2: stable sorting keeps original row labels increasing within a fiber. -/
theorem stable_tie_increasing {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) {i j : Fin N} (hij : i < j)
    (heq : sortedKey f i = sortedKey f j) : stableSort f i < stableSort f j := by
  exact (Tuple.eq_sort_iff.mp (rfl : stableSort f = Tuple.sort f)).2 i j hij heq

/-- S3: the exact position interval of a complete key. -/
theorem sorted_fiber_interval {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (w : W) (i : Fin N) :
    sortedKey f i = w ↔ lowerRank f w ≤ i.val ∧ i.val < lowerRank f w + keyCount f w := by
  classical
  let g := sortedKey f
  have hm : Monotone g := Tuple.monotone_sort f
  have hreindex (P : W → Prop) [DecidablePred P] :
      (univ.filter fun j => P (g j)).card = (univ.filter fun j => P (f j)).card := by
    let e : {j : Fin N // P (g j)} ≃ {j : Fin N // P (f j)} :=
      (stableSort f).subtypeEquiv (fun _ => Iff.rfl)
    simpa only [Fintype.card_subtype] using Fintype.card_congr e
  have hlt (j : Fin N) : g j < w ↔ j.val < lowerRank f w := by
    have hcard : (univ.filter fun l => g l < w).card = lowerRank f w := by
      simpa only [lowerRank] using hreindex (fun x => x < w)
    rw [← hcard]
    constructor
    · intro h
      have hs : Iic j ⊆ univ.filter (fun l => g l < w) := by
        intro l hl
        exact mem_filter.mpr ⟨mem_univ _, (hm (mem_Iic.mp hl)).trans_lt h⟩
      have hc := card_le_card hs
      rw [Fin.card_Iic] at hc
      omega
    · intro h
      apply Classical.byContradiction
      intro hn
      have hs : univ.filter (fun l => g l < w) ⊆ Iio j := by
        intro l hl
        apply mem_Iio.mpr
        apply Classical.byContradiction
        intro hlj
        exact hn ((hm (le_of_not_gt hlj)).trans_lt (mem_filter.mp hl).2)
      have hc := card_le_card hs
      rw [Fin.card_Iio] at hc
      omega
  have hcardle : (univ.filter fun j => f j ≤ w).card = lowerRank f w + keyCount f w := by
    have hd : Disjoint (univ.filter fun j => f j < w) (univ.filter fun j => f j = w) := by
      apply disjoint_left.mpr
      intro j hj hk
      exact (ne_of_lt (mem_filter.mp hj).2) (mem_filter.mp hk).2
    have hs : univ.filter (fun j => f j ≤ w) =
        (univ.filter fun j => f j < w) ∪ (univ.filter fun j => f j = w) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_union, le_iff_lt_or_eq]
    rw [hs, card_union_of_disjoint hd]
    rfl
  have hle (j : Fin N) : g j ≤ w ↔ j.val < lowerRank f w + keyCount f w := by
    have h := Tuple.lt_card_le_iff_apply_le_of_monotone g w hm j
    have hcard : Fintype.card {x : Fin N // g x ≤ w} = lowerRank f w + keyCount f w := by
      rw [Fintype.card_subtype]
      have hr := hreindex (fun x => x ≤ w)
      have hr' : (univ.filter fun j => g j ≤ w).card = (univ.filter fun j => f j ≤ w).card := by
        simpa only using hr
      exact hr'.trans hcardle
    rw [hcard] at h
    exact h.symm
  constructor
  · intro h
    have hg : g i = w := h
    refine ⟨?_, (hle i).mp hg.le⟩
    apply Nat.le_of_not_gt
    intro hi
    exact (ne_of_lt ((hlt i).mpr hi)) hg
  · intro h
    apply le_antisymm ((hle i).mpr h.2)
    apply le_of_not_gt
    intro hi
    exact Nat.not_lt_of_ge h.1 ((hlt i).mp hi)

/-- S4: copies of a complete word force an observable contiguous increasing run. -/
theorem full_word_forces_run {N : ℕ} {W : Type*} [LinearOrder W]
    (f : Fin N → W) (w : W) (m : ℕ) (_hm : 1 ≤ m) (hc : m ≤ keyCount f w) :
    HasIncreasingRun (stableSort f) m := by
  classical
  have hd : Disjoint (univ.filter fun j => f j < w) (univ.filter fun j => f j = w) := by
    apply disjoint_left.mpr
    intro j hj hk
    exact (ne_of_lt (mem_filter.mp hj).2) (mem_filter.mp hk).2
  have htotal : lowerRank f w + keyCount f w ≤ N := by
    change (univ.filter fun j => f j < w).card + (univ.filter fun j => f j = w).card ≤ N
    rw [← card_union_of_disjoint hd]
    exact (card_le_card (subset_univ _)).trans_eq (card_univ.trans (Fintype.card_fin N))
  refine ⟨lowerRank f w, by omega, ?_⟩
  intro i j hi hj hij
  apply stable_tie_increasing f hij
  have hiw : sortedKey f i = w := (sorted_fiber_interval f w i).mpr ⟨hi, by
    have hij' : i.val < j.val := hij
    omega⟩
  have hjw : sortedKey f j = w := (sorted_fiber_interval f w j).mpr ⟨by
    have hij' : i.val < j.val := hij
    omega, by omega⟩
  exact hiw.trans hjw.symm

end RiffleLower
