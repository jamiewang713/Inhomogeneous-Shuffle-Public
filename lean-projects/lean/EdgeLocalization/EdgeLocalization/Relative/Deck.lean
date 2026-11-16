import EdgeLocalization.Relative.Model
import EdgeLocalization.Collision.Rows

/-! Frozen relative-coordinate deck theorems R.01–R.07. -/

namespace EdgeLocalization

theorem relativeInternalEdges_subset_range (N : ℕ) (rows : ℕ → List ℕ)
    (xList : List ℕ) (s : ℕ) :
    relativeInternalEdges N rows xList s ⊆ Finset.range (N - 1) := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

theorem relativeInternalEdges_zero_shift (N : ℕ) (rows : ℕ → List ℕ)
    (xList : List ℕ) :
    relativeInternalEdges N rows xList 0 = internalEdges N rows xList := by
  ext i
  constructor
  · intro hi
    simpa only [Nat.add_zero] using (Finset.mem_filter.mp hi).2
  · intro hi
    exact Finset.mem_filter.mpr
      ⟨internalEdges_subset_range N rows xList hi, by simpa only [Nat.add_zero] using hi⟩

theorem relativeInternalEdges_card_le (N : ℕ) (rows : ℕ → List ℕ)
    (xList : List ℕ) (s : ℕ) :
    (relativeInternalEdges N rows xList s).card ≤ (internalEdges N rows xList).card := by
  apply Finset.card_le_card_of_injOn (fun i => i + s)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact Nat.add_right_cancel hij

theorem ambientLeft_le_deck_size (N : ℕ) (rows : ℕ → List ℕ) (wList : List ℕ) :
    ambientLeft N rows wList ≤ N := by
  calc
    _ ≤ (Finset.range N).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := Finset.card_range N

theorem ambientLeft_nil (N : ℕ) (rows : ℕ → List ℕ) :
    ambientLeft N rows [] = 0 := by
  have h : (Finset.range N).filter (fun i => rows i < []) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨_, hlt⟩
    change List.Lex (· < ·) (rows i) [] at hlt
    exact List.not_lex_nil hlt
  simp only [ambientLeft, h, Finset.card_empty]

theorem matrix_ambientLeft_le_internal_edge {N K k : ℕ}
    (n : Fin K → Fin k → ℕ) (ω : FixedMatrix N n)
    (wList xList : List ℕ) (hprefix : wList <+: xList)
    (i : ℕ) (hi : i ∈ internalEdges N (sortedRows n ω) xList) :
    ambientLeft N (sortedRows n ω) wList ≤ i := by
  have hiEdge := Finset.mem_range.mp (internalEdges_subset_range N (sortedRows n ω) xList hi)
  have hiN : i < N := by omega
  have hwp : wList <+: sortedRows n ω i :=
    hprefix.trans (Finset.mem_filter.mp hi).2.2
  have hwle : wList ≤ sortedRows n ω i := by
    rcases hwp with ⟨tail, htail⟩
    rw [← htail]
    cases tail with
    | nil => simp
    | cons a tail =>
      apply le_of_lt
      simpa only [List.append_nil] using
        (List.Lex.append_left (· < ·)
          (List.Lex.nil : List.Lex (· < ·) [] (a :: tail)) wList)
  calc
    _ ≤ (Finset.range i).card := by
      apply Finset.card_le_card
      intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hjRange, hjlt⟩
      have hjN : j < N := Finset.mem_range.mp hjRange
      apply Finset.mem_range.mpr
      by_contra hji
      have hij : i ≤ j := by omega
      have hsort := sortPermutation_monotone_rows (rawRow n ω)
        ⟨i, hiN⟩ ⟨j, hjN⟩ hij
      have hrows : sortedRows n ω i ≤ sortedRows n ω j := by
        simpa only [sortedRows, rowsOfLabels, dif_pos hiN, dif_pos hjN] using hsort
      exact (not_lt_of_ge (le_trans hwle hrows)) hjlt
    _ = i := Finset.card_range i

theorem matrix_relativeInternalEdges_card_eq {N K k : ℕ}
    (n : Fin K → Fin k → ℕ) (ω : FixedMatrix N n)
    (wList xList : List ℕ) (hprefix : wList <+: xList) :
    (relativeInternalEdges N (sortedRows n ω) xList
      (ambientLeft N (sortedRows n ω) wList)).card =
      (internalEdges N (sortedRows n ω) xList).card := by
  let s := ambientLeft N (sortedRows n ω) wList
  change (relativeInternalEdges N (sortedRows n ω) xList s).card = _
  apply le_antisymm (relativeInternalEdges_card_le N (sortedRows n ω) xList s)
  apply Finset.card_le_card_of_injOn (fun j => j - s)
  · intro j hj
    have hsj : s ≤ j := matrix_ambientLeft_le_internal_edge n ω wList xList hprefix j hj
    have hjRange := Finset.mem_range.mp
      (internalEdges_subset_range N (sortedRows n ω) xList hj)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt (Nat.sub_le j s) hjRange), ?_⟩
    simpa only [Nat.sub_add_cancel hsj] using hj
  · intro i hi j hj hij
    have hsi : s ≤ i := matrix_ambientLeft_le_internal_edge n ω wList xList hprefix i hi
    have hsj : s ≤ j := matrix_ambientLeft_le_internal_edge n ω wList xList hprefix j hj
    have h := congrArg (fun t => t + s) hij
    simpa only [Nat.sub_add_cancel hsi, Nat.sub_add_cancel hsj] using h

end EdgeLocalization
