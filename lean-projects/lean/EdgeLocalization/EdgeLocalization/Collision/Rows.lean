import EdgeLocalization.Collision.Model
import EdgeLocalization.Deck
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Lex
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals

namespace EdgeLocalization

/-- C.18: vector prefixes retain their coordinate length. -/
theorem prefixWord_length {M k : ℕ} (x : Fin M → Fin k) :
    (prefixWord x).length = M := by
  simp [prefixWord]

/-- C.19: every original row contains exactly the given shuffle columns. -/
theorem rawRow_length {N K k : ℕ} (n : Fin K → Fin k → ℕ)
    (ω : FixedMatrix N n) (i : Fin N) : (rawRow n ω i).length = K := by
  simp [rawRow]

/-- C.20a: the natural-index adapter agrees with every actual row label. -/
theorem rowsOfLabels_apply {N : ℕ} (R : Fin N → List ℕ) (i : Fin N) :
    rowsOfLabels R i.val = R i := by
  simp [rowsOfLabels]

/-- C.20b: the adapter's prescribed value outside the deck is the empty list. -/
theorem rowsOfLabels_outside {N : ℕ} (R : Fin N → List ℕ) (t : ℕ)
    (ht : N ≤ t) : rowsOfLabels R t = [] := by
  simp [rowsOfLabels, Nat.not_lt.mpr ht]

/-- C.21: list-prefix membership is exactly the prescribed initial coordinates. -/
theorem prefixWord_prefix_rawRow_iff {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (x : Fin M → Fin k)
    (ω : FixedMatrix N n) (i : Fin N) :
    prefixWord x <+: rawRow n ω i ↔
      ∀ t : Fin M, (ω (Fin.castLE hM t)).val i = x t := by
  rw [List.prefix_iff_getElem]
  constructor
  · rintro ⟨_, h⟩ t
    have ht := h t.val (by simp [prefixWord])
    apply Fin.ext
    simpa [prefixWord, rawRow] using ht.symm
  · intro h
    refine ⟨by simpa [prefixWord, rawRow] using hM, ?_⟩
    intro j hj
    have hjM : j < M := by simpa [prefixWord] using hj
    have ht := congrArg Fin.val (h ⟨j, hjM⟩)
    simpa [prefixWord, rawRow] using ht.symm

/-- C.22: full row equality is coordinatewise digit equality. -/
theorem rawRow_eq_iff {N K k : ℕ} (n : Fin K → Fin k → ℕ)
    (ω : FixedMatrix N n) (i j : Fin N) :
    rawRow n ω i = rawRow n ω j ↔
      ∀ t : Fin K, (ω t).val i = (ω t).val j := by
  simp only [rawRow, List.ofFn_inj]
  constructor
  · intro h t
    apply Fin.ext
    exact congrFun h t
  · intro h
    funext t
    exact congrArg Fin.val (h t)

/-- C.23: the vector representation covers every list in the alphabet. -/
theorem prefixWord_represents_list {k : ℕ} (xList : List ℕ)
    (hx : ∀ a ∈ xList, a < k) :
    ∃ x : Fin xList.length → Fin k, prefixWord x = xList := by
  refine ⟨fun i => ⟨xList.get i, hx _ (List.get_mem _ _)⟩, ?_⟩
  exact List.ofFn_get xList

/-- C.D09: sort the original labels by the lexicographic order of their row words. -/
def sortedLabels {N : ℕ} (R : Fin N → List ℕ) : List (Fin N) :=
  (List.finRange N).mergeSort (fun i j => decide (R i ≤ R j))

/-- C.25: sorting retains each original label exactly once. -/
theorem sortedLabels_perm {N : ℕ} (R : Fin N → List ℕ) :
    (sortedLabels R).Perm (List.finRange N) := by
  exact List.mergeSort_perm _ _

/-- C.24: sorting retains the deck size, including an empty deck. -/
theorem sortedLabels_length {N : ℕ} (R : Fin N → List ℕ) :
    (sortedLabels R).length = N := by
  exact (sortedLabels_perm R).length_eq.trans List.length_finRange

/-- C.26: the sorted labels form a duplicate-free enumeration of the labels. -/
theorem sortedLabels_nodup_mem {N : ℕ} (R : Fin N → List ℕ) :
    (sortedLabels R).Nodup ∧ ∀ i : Fin N, i ∈ sortedLabels R := by
  exact ⟨(sortedLabels_perm R).nodup_iff.mpr (List.nodup_finRange N),
    fun i => (sortedLabels_perm R).mem_iff.mpr (List.mem_finRange i)⟩

/-- C.D10: the sorting position maps to its original row label. -/
def sortPermutation {N : ℕ} (R : Fin N → List ℕ) : Equiv.Perm (Fin N) :=
  (finCongr (sortedLabels_length R).symm).trans
    (List.Nodup.getEquivOfForallMemList (sortedLabels R)
      (sortedLabels_nodup_mem R).1 (sortedLabels_nodup_mem R).2)

/-- C.27: the constructed permutation really orders the row words. -/
theorem sortPermutation_monotone_rows {N : ℕ} (R : Fin N → List ℕ)
    (i j : Fin N) (hij : i ≤ j) :
    R (sortPermutation R i) ≤ R (sortPermutation R j) := by
  let r : Fin N → Fin N → Prop := fun a b => R a ≤ R b
  letI : IsTotal (Fin N) r := ⟨fun a b => le_total (R a) (R b)⟩
  letI : IsTrans (Fin N) r := ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  letI : IsRefl (Fin N) r := ⟨fun _ => le_rfl⟩
  have hs : List.Sorted r (sortedLabels R) :=
    List.sorted_mergeSort' r (List.finRange N)
  change r ((sortedLabels R).get (Fin.cast (sortedLabels_length R).symm i))
    ((sortedLabels R).get (Fin.cast (sortedLabels_length R).symm j))
  exact hs.rel_get_of_le hij

/-- C.D11: the actual lexicographically sorted matrix rows in natural positions. -/
def sortedRows {N K k : ℕ} (n : Fin K → Fin k → ℕ)
    (ω : FixedMatrix N n) : ℕ → List ℕ :=
  rowsOfLabels (fun i => rawRow n ω (sortPermutation (rawRow n ω) i))

/-- C.28: a row permutation preserves prefix occupancy cardinality. -/
theorem occupied_card_reindex {N : ℕ} (R : Fin N → List ℕ)
    (e : Equiv.Perm (Fin N)) (xList : List ℕ) :
    (occupied N (rowsOfLabels (R ∘ e)) xList).card =
      (occupied N (rowsOfLabels R) xList).card := by
  classical
  refine Finset.card_bij'
    (fun i hi => (e ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩).val)
    (fun i hi => (e.symm ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩).val)
    ?_ ?_ ?_ ?_
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hiN, hx⟩
    have hiN' := Finset.mem_range.mp hiN
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (e ⟨i, hiN'⟩).isLt, ?_⟩
    simpa [rowsOfLabels, hiN', Function.comp_def] using hx
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hiN, hx⟩
    have hiN' := Finset.mem_range.mp hiN
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (e.symm ⟨i, hiN'⟩).isLt, ?_⟩
    simpa [rowsOfLabels, hiN', Function.comp_def] using hx
  · intro i hi
    simp
  · intro i hi
    simp

/-- C.29: sorting the two image labels preserves unordered collision counts. -/
theorem collisionPairs_card_reindex {N : ℕ} (R : Fin N → List ℕ)
    (e : Equiv.Perm (Fin N)) (xList : List ℕ) :
    (collisionPairs N (rowsOfLabels (R ∘ e)) xList).card =
      (collisionPairs N (rowsOfLabels R) xList).card := by
  classical
  let pairs (S : Fin N → List ℕ) : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun p => p.1 < p.2 ∧ S p.1 = S p.2 ∧ xList <+: S p.1)
  have hcard (S : Fin N → List ℕ) :
      (collisionPairs N (rowsOfLabels S) xList).card = (pairs S).card := by
    refine Finset.card_bij
      (fun p hp =>
        (⟨p.1, Finset.mem_range.mp (Finset.mem_product.mp
          (Finset.mem_filter.mp hp).1).1⟩,
         ⟨p.2, Finset.mem_range.mp (Finset.mem_product.mp
          (Finset.mem_filter.mp hp).1).2⟩)) ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpN, hpLt, hpEq, hpX⟩
      rcases Finset.mem_product.mp hpN with ⟨hp1, hp2⟩
      have hp1N := Finset.mem_range.mp hp1
      have hp2N := Finset.mem_range.mp hp2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hpLt, ?_, ?_⟩
      · simpa [rowsOfLabels, hp1N, hp2N] using hpEq
      · simpa [rowsOfLabels, hp1N] using hpX
    · intro p hp q hq hpq
      exact congrArg (fun z : Fin N × Fin N => (z.1.val, z.2.val)) hpq
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨_, hpLt, hpEq, hpX⟩
      have hmem : (p.1.val, p.2.val) ∈
          collisionPairs N (rowsOfLabels S) xList := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr p.1.isLt, Finset.mem_range.mpr p.2.isLt⟩,
          hpLt, ?_, ?_⟩
        · simpa only [rowsOfLabels_apply] using hpEq
        · simpa only [rowsOfLabels_apply] using hpX
      exact ⟨(p.1.val, p.2.val), hmem, rfl⟩
  rw [hcard, hcard]
  let orient (π : Equiv.Perm (Fin N)) (p : Fin N × Fin N) : Fin N × Fin N :=
    (min (π p.1) (π p.2), max (π p.1) (π p.2))
  have hmem (S : Fin N → List ℕ) (π : Equiv.Perm (Fin N))
      (p : Fin N × Fin N) (hp : p ∈ pairs (S ∘ π)) :
      orient π p ∈ pairs S := by
    rcases Finset.mem_filter.mp hp with ⟨_, hpLt, hpEq, hpX⟩
    have hne : π p.1 ≠ π p.2 := fun h => (ne_of_lt hpLt) (π.injective h)
    by_cases hle : π p.1 ≤ π p.2
    · have hlt : π p.1 < π p.2 := lt_of_le_of_ne hle hne
      simp only [orient, min_eq_left hle, max_eq_right hle, pairs,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hlt, hpEq, hpX⟩
    · have hlt : π p.2 < π p.1 := lt_of_not_ge hle
      simp only [orient, min_eq_right hlt.le, max_eq_left hlt.le, pairs,
        Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hlt, hpEq.symm, ?_⟩
      have hpX' : xList <+: (S ∘ π) p.2 := hpEq ▸ hpX
      exact hpX'
  have hinv (π : Equiv.Perm (Fin N)) (p : Fin N × Fin N) (hp : p.1 < p.2) :
      orient π.symm (orient π p) = p := by
    by_cases hle : π p.1 ≤ π p.2
    · simp [orient, min_eq_left hle, max_eq_right hle,
        min_eq_left hp.le, max_eq_right hp.le]
    · have hle' : π p.2 ≤ π p.1 := le_of_lt (lt_of_not_ge hle)
      simp [orient, min_eq_right hle', max_eq_left hle',
        min_eq_right hp.le, max_eq_left hp.le]
  refine Finset.card_bij' (fun p _ => orient e p) (fun p _ => orient e.symm p)
    (fun p hp => hmem R e p hp) ?_ ?_ ?_
  · intro p hp
    apply hmem (R ∘ e) e.symm p
    simpa [Function.comp_def] using hp
  · intro p hp
    exact hinv e p (Finset.mem_filter.mp hp).2.1
  · intro p hp
    simpa using hinv e.symm p (Finset.mem_filter.mp hp).2.1

/-- C.30: the sorted and original decks have the same prefix occupancy. -/
theorem sorted_occupancy_eq_raw {N K k : ℕ} (n : Fin K → Fin k → ℕ)
    (ω : FixedMatrix N n) (xList : List ℕ) :
    occupancyCount N (sortedRows n ω) xList =
      occupancyCount N (rawRows n ω) xList := by
  exact occupied_card_reindex (rawRow n ω) (sortPermutation (rawRow n ω)) xList

/-- C.31: the sorted and original decks have the same unordered collisions. -/
theorem sorted_collisionPairs_card_eq_raw {N K k : ℕ} (n : Fin K → Fin k → ℕ)
    (ω : FixedMatrix N n) (xList : List ℕ) :
    (collisionPairs N (sortedRows n ω) xList).card =
      (collisionPairs N (rawRows n ω) xList).card := by
  exact collisionPairs_card_reindex (rawRow n ω) (sortPermutation (rawRow n ω)) xList

/-- C.36: collision pairs are indexed by increasing positions in the deck. -/
theorem collisionPairs_subset_increasing (N : ℕ) (rows : ℕ → List ℕ)
    (xList : List ℕ) :
    collisionPairs N rows xList ⊆
      ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 < p.2) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpN, hpLt, _⟩
  exact Finset.mem_filter.mpr ⟨hpN, hpLt⟩

/-- C.37: each unordered pair has exactly one increasing orientation. -/
theorem increasing_pair_card (N : ℕ) :
    (((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 < p.2)).card =
      Nat.choose N 2 := by
  calc
    _ = ∑ j ∈ Finset.range N, j := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      have hf : (Finset.range N).filter (fun i => i < j) = Finset.range j := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        have hjN := Finset.mem_range.mp hj
        omega
      rw [hf]
      simp
    _ = Nat.choose N 2 := by rw [Finset.sum_range_id, Nat.choose_two_right]

/-- C.48: a deck with no rows has no distinct collision pair. -/
theorem collisionPairs_zero (rows : ℕ → List ℕ) (xList : List ℕ) :
    collisionPairs 0 rows xList = ∅ := by
  simp [collisionPairs]

/-- C.49: a deck with one row has no distinct collision pair. -/
theorem collisionPairs_one (rows : ℕ → List ℕ) (xList : List ℕ) :
    collisionPairs 1 rows xList = ∅ := by
  simp [collisionPairs]

end EdgeLocalization
