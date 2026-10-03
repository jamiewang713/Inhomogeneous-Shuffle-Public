import RiffleShuffle.Words
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open scoped BigOperators
namespace RiffleShuffle

variable {N k K : ℕ} {P : PileProfile N k K}

/-- Labelled rows, with exactly the prescribed count in every column. -/
structure ShuffleMatrix (P : PileProfile N k K) where
  rows : Fin N → Word k K
  column_count : ∀ (j : Fin K) (a : Fin k),
    (Finset.univ.filter fun i => (rows i).get j = a).card = P.count j a

/-- M01: the column sums are the complete finite feasibility condition. -/
theorem shuffleMatrix_nonempty (P : PileProfile N k K) : Nonempty (ShuffleMatrix P) := by
  classical
  let e (j : Fin K) : Fin N ≃ (Σ a : Fin k, Fin (P.count j a)) :=
    Fintype.equivOfCardEq (by simp [P.total j])
  let rows (i : Fin N) : Word k K := List.Vector.ofFn fun j => (e j i).1
  refine ⟨⟨rows, ?_⟩⟩
  intro j a
  let fiber : {b : (Σ a : Fin k, Fin (P.count j a)) // b.1 = a} ≃ Fin (P.count j a) :=
    { toFun := fun b => by
        rcases b with ⟨⟨b, t⟩, h⟩
        change b = a at h
        subst b
        exact t
      invFun := fun t => ⟨⟨a, t⟩, rfl⟩
      left_inv := by rintro ⟨⟨b, t⟩, h⟩; change b = a at h; subst b; rfl
      right_inv := by intro t; rfl }
  have hc := Fintype.card_congr
    ((Equiv.subtypeEquivOfSubtype (p := fun b => b.1 = a) (e j)).trans fiber)
  simpa [Fintype.card_subtype, rows, List.Vector.get_ofFn] using hc

namespace ShuffleMatrix

def sortPerm (S : ShuffleMatrix P) : Equiv.Perm (Fin N) := Tuple.sort S.rows

def sortedRows (S : ShuffleMatrix P) : Fin N → Word k K := S.rows ∘ S.sortPerm

/-- M02. -/
theorem row_legal (S : ShuffleMatrix P) (i : Fin N) : Legal P (S.rows i) := by
  classical
  refine ⟨le_rfl, fun j => ?_⟩
  have hp : 0 < (Finset.univ.filter fun r => (S.rows r).get j = (S.rows i).get j).card :=
    Finset.card_pos.mpr ⟨i, by simp⟩
  rw [S.column_count] at hp
  simpa [PileProfile.countAt, j.isLt] using hp

/-- M03. -/
theorem reindex_counts (S : ShuffleMatrix P) (σ : Equiv.Perm (Fin N))
    (j : Fin K) (a : Fin k) :
    (Finset.univ.filter fun i => (S.rows (σ i)).get j = a).card = P.count j a := by
  classical
  calc
    _ = (Finset.univ.filter fun i => (S.rows i).get j = a).card := by
      apply Finset.card_bij (fun i _ => σ i)
      · intro i hi; simpa using hi
      · intro i hi l hl hil; exact σ.injective hil
      · intro i hi; refine ⟨σ.symm i, ?_, by simp⟩; simpa using hi
    _ = _ := S.column_count j a

def reindex (S : ShuffleMatrix P) (σ : Equiv.Perm (Fin N)) : ShuffleMatrix P :=
  ⟨S.rows ∘ σ, S.reindex_counts σ⟩

/-- M04. -/
theorem sorted_monotone (S : ShuffleMatrix P) : Monotone S.sortedRows :=
  Tuple.monotone_sort S.rows

/-- M05. -/
theorem sorted_row_legal (S : ShuffleMatrix P) (i : Fin N) : Legal P (S.sortedRows i) :=
  S.row_legal (S.sortPerm i)

/-- M06. -/
theorem sort_preserves_count (S : ShuffleMatrix P) (Q : Word k K → Prop) :
    letI : DecidablePred Q := Classical.decPred Q
    (Finset.univ.filter fun i => Q (S.sortedRows i)).card =
      (Finset.univ.filter fun i => Q (S.rows i)).card := by
  classical
  apply Finset.card_bij (fun i _ => S.sortPerm i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj hij; exact S.sortPerm.injective hij
  · intro i hi
    refine ⟨S.sortPerm.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    change Q (S.rows (S.sortPerm (S.sortPerm.symm i)))
    simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hi).2


/-- Zero-based ranks belonging to a legal prefix cylinder. -/
def rankSet (S : ShuffleMatrix P) (x : Node P) : Finset (Fin N) :=
  Finset.univ.filter fun i => x.toList <+: (S.sortedRows i).toList

def lowerEndpoint (S : ShuffleMatrix P) (x : Node P) : ℕ :=
  (Finset.univ.filter fun i => (S.sortedRows i).toList.take x.depth < x.toList).card

def upperEndpoint (S : ShuffleMatrix P) (x : Node P) : ℕ :=
  (Finset.univ.filter fun i => (S.sortedRows i).toList.take x.depth ≤ x.toList).card

/-- M07: comparison with the truncated rows includes strict full-row extensions. -/
theorem rank_mem_iff (S : ShuffleMatrix P) (x : Node P) (i : Fin N) :
    i ∈ S.rankSet x ↔ S.lowerEndpoint x ≤ i.val ∧ i.val < S.upperEndpoint x := by
  classical
  have hx : x.toList.length = x.depth := List.Vector.toList_length x.word
  have hm : Monotone (fun i : Fin N => (S.sortedRows i).toList.take x.depth) := by
    intro a b hab
    exact take_lex_monotone x.depth (S.sorted_monotone hab)
  have hl := Tuple.lt_card_lt_iff_apply_lt_of_monotone (a := x.toList) (j := i) hm
  have hu := Tuple.lt_card_le_iff_apply_le_of_monotone (a := x.toList) (j := i) hm
  change (i ∈ Finset.univ.filter fun i => x.toList <+: (S.sortedRows i).toList) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.prefix_iff_eq_take, hx]
  change i.val < S.lowerEndpoint x ↔ _ at hl
  change i.val < S.upperEndpoint x ↔ _ at hu
  constructor
  · intro he
    constructor
    · apply Nat.le_of_not_gt
      intro h
      have := hl.mp h
      rw [← he] at this
      exact lt_irrefl _ this
    · apply hu.mpr
      rw [he]
  · rintro ⟨hlo, hup⟩
    apply le_antisymm
    · exact le_of_not_gt (fun h => (Nat.not_lt_of_ge hlo) (hl.mpr h))
    · exact hu.mp hup

/-- M08: valid also for empty realized prefix blocks. -/
theorem rank_count (S : ShuffleMatrix P) (x : Node P) :
    (S.rankSet x).card = S.upperEndpoint x - S.lowerEndpoint x := by
  classical
  let A : Finset (Fin N) := Finset.univ.filter fun i =>
    (S.sortedRows i).toList.take x.depth < x.toList
  let B : Finset (Fin N) := Finset.univ.filter fun i =>
    (S.sortedRows i).toList.take x.depth ≤ x.toList
  have hAB : A ⊆ B := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt (Finset.mem_filter.mp hi).2⟩
  have he : S.rankSet x = B \ A := by
    ext i
    have hx : x.toList.length = x.depth := List.Vector.toList_length x.word
    simp only [rankSet, A, B, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
      true_and, List.prefix_iff_eq_take, hx, not_lt]
    exact eq_iff_le_not_lt.trans (by simp only [not_lt, and_comm])
  rw [he, Finset.card_sdiff_of_subset hAB]
  rfl

/-- M09. -/
theorem endpoint_bounds (S : ShuffleMatrix P) (x : Node P) :
    0 ≤ S.lowerEndpoint x ∧ S.lowerEndpoint x ≤ S.upperEndpoint x ∧ S.upperEndpoint x ≤ N := by
  classical
  refine ⟨Nat.zero_le _, ?_, ?_⟩
  · apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt (Finset.mem_filter.mp hi).2⟩
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin N)

/-- M10. -/
theorem rank_convex (S : ShuffleMatrix P) (x : Node P) {i j l : Fin N}
    (hij : i ≤ j) (hjl : j ≤ l) (hi : i ∈ S.rankSet x) (hl : l ∈ S.rankSet x) :
    j ∈ S.rankSet x := by
  rw [S.rank_mem_iff] at hi hl ⊢
  exact ⟨hi.1.trans hij, lt_of_le_of_lt hjl hl.2⟩

/-- M11. -/
theorem rank_mono (S : ShuffleMatrix P) {x y : Node P} (h : x.IsPrefix y) :
    S.rankSet y ⊆ S.rankSet x := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (Finset.mem_filter.mp hi).2⟩

/-- M12. -/
theorem rank_disjoint (S : ShuffleMatrix P) {x y : Node P}
    (hxy : ¬ x.IsPrefix y) (hyx : ¬ y.IsPrefix x) :
    Disjoint (S.rankSet x) (S.rankSet y) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rcases List.prefix_or_prefix_of_prefix (Finset.mem_filter.mp hi).2
    (Finset.mem_filter.mp hj).2 with h | h
  · exact hxy h
  · exact hyx h

end ShuffleMatrix
end RiffleShuffle
