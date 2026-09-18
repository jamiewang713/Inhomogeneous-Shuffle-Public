import Mathlib.Tactic
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

namespace EdgeLocalization

/-- D3: zero-based positions whose rows have the specified prefix. -/
def occupied (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => x <+: rows i)

/-- D4: equal adjacent rows carrying the specified prefix. -/
def internalEdges (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) : Finset ℕ :=
  (Finset.range (N - 1)).filter (fun i => rows i = rows (i + 1) ∧ x <+: rows i)

/-- D4: all equal-row adjacencies in the deck. -/
def allEdges (N : ℕ) (rows : ℕ → List ℕ) : Finset ℕ :=
  internalEdges N rows []

/-- D4: unordered equal-row pairs represented by their increasing indices. -/
def collisionPairs (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N) ×ˢ (Finset.range N)).filter
    (fun p => p.1 < p.2 ∧ rows p.1 = rows p.2 ∧ x <+: rows p.1)

/-- D5: the number of internal edges. -/
def edgeCount (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) : ℕ :=
  (internalEdges N rows x).card

/-- D5: the number of occupied row positions. -/
def occupancyCount (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) : ℕ :=
  (occupied N rows x).card

/-- F14: the left endpoint of every internal edge is occupied. -/
theorem internalEdges_subset_occupied (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) :
    internalEdges N rows x ⊆ occupied N rows x := by
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hi, _, hx⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, hx⟩
  have hiN := Finset.mem_range.mp hi
  omega

/-- F15: every internal edge index lies in the path edge range. -/
theorem internalEdges_subset_range (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) :
    internalEdges N rows x ⊆ Finset.range (N - 1) := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

/-- F16: edge count is at most occupancy, including empty decks. -/
theorem internalEdges_card_le_occupancy (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) :
    (internalEdges N rows x).card ≤ (occupied N rows x).card := by
  exact Finset.card_le_card (internalEdges_subset_occupied N rows x)

/-- F17: a deck of size zero has no internal edges. -/
theorem internalEdges_zero (rows : ℕ → List ℕ) (x : List ℕ) :
    internalEdges 0 rows x = ∅ := by
  simp [internalEdges]

/-- F18: a deck of size one has no internal edges. -/
theorem internalEdges_one (rows : ℕ → List ℕ) (x : List ℕ) :
    internalEdges 1 rows x = ∅ := by
  simp [internalEdges]

/-- F19: equal rows have the same prefixes. -/
theorem equal_rows_prefix_transfer (rows : ℕ → List ℕ) (x : List ℕ) (i j : ℕ)
    (hij : rows i = rows j) (hx : x <+: rows i) : x <+: rows j := by
  simpa only [hij] using hx

/-- F20: an equal-row edge is internal exactly when its left endpoint is occupied. -/
theorem localize_internal_edge (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) (i : ℕ) :
    i ∈ internalEdges N rows x ↔ i ∈ allEdges N rows ∧ i ∈ occupied N rows x := by
  constructor
  · intro hi
    refine ⟨?_, internalEdges_subset_occupied N rows x hi⟩
    rcases Finset.mem_filter.mp hi with ⟨hi, heq, _⟩
    apply Finset.mem_filter.mpr
    exact ⟨hi, heq, List.nil_prefix⟩
  · rintro ⟨hi, hx⟩
    rcases Finset.mem_filter.mp hi with ⟨hi, heq, _⟩
    exact Finset.mem_filter.mpr ⟨hi, heq, (Finset.mem_filter.mp hx).2⟩

/-- F21: mapping an internal edge to its two positions injects it into collision pairs. -/
theorem internalEdges_card_le_collisionPairs
    (N : ℕ) (rows : ℕ → List ℕ) (x : List ℕ) :
    (internalEdges N rows x).card ≤ (collisionPairs N rows x).card := by
  apply Finset.card_le_card_of_injOn (fun i => (i, i + 1))
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi, heq, hx⟩
    have hiN := Finset.mem_range.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,
      Finset.mem_range.mpr ?_⟩, ?_, heq, hx⟩ <;> dsimp only <;> omega
  · intro i hi j hj hij
    exact congrArg Prod.fst hij

end EdgeLocalization
