import RiffleShuffle.Matrices
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Equality-adjacency shuffle graphs; frozen items G01–G07. -/

noncomputable section
namespace RiffleShuffle
namespace ShuffleMatrix

variable {N k K : ℕ} {P : PileProfile N k K}

def shuffleGraph (S : ShuffleMatrix P) : SimpleGraph (Fin N) where
  Adj i j := (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ S.sortedRows i = S.sortedRows j
  symm := by
    constructor
    intro i j h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro i h
    rcases h.1 with h | h <;> omega

/-- Spanning restriction: ranks outside the prefix block are isolated. -/
def blockGraph (S : ShuffleMatrix P) (x : Node P) : SimpleGraph (Fin N) where
  Adj i j := S.shuffleGraph.Adj i j ∧ i ∈ S.rankSet x ∧ j ∈ S.rankSet x
  symm := by
    constructor
    intro i j h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro i h
    exact S.shuffleGraph.irrefl h.1

def sharedGraph (S T : ShuffleMatrix P) : SimpleGraph (Fin N) :=
  S.shuffleGraph ⊓ T.shuffleGraph

/-- G01. -/
theorem graph_adj_iff (S : ShuffleMatrix P) (i j : Fin N) :
    S.shuffleGraph.Adj i j ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ S.sortedRows i = S.sortedRows j := Iff.rfl

/-- G02. -/
theorem graph_subpath (S : ShuffleMatrix P) {i j : Fin N} (h : S.shuffleGraph.Adj i j) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := h.1

/-- G03. -/
theorem adj_same_prefix (S : ShuffleMatrix P) (x : Node P) {i j : Fin N}
    (h : S.shuffleGraph.Adj i j) : i ∈ S.rankSet x ↔ j ∈ S.rankSet x := by
  simp only [rankSet, Finset.mem_filter, Finset.mem_univ, true_and, h.2]

/-- G04: a constant-word class is convex in sorted rank order. -/
theorem equal_rows_between (S : ShuffleMatrix P) {i j l : Fin N}
    (hij : i ≤ j) (hjl : j ≤ l) (h : S.sortedRows i = S.sortedRows l) :
    S.sortedRows j = S.sortedRows i := by
  apply le_antisymm
  · exact (S.sorted_monotone hjl).trans_eq h.symm
  · exact S.sorted_monotone hij

/-- G05: the graph components are precisely the full-word equality classes. -/
theorem reachable_iff_eq (S : ShuffleMatrix P) (i j : Fin N) :
    S.shuffleGraph.Reachable i j ↔ S.sortedRows i = S.sortedRows j := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | cons h p ih => exact h.2.trans ih
  · intro heq
    have forward : ∀ (d : ℕ) (u v : Fin N), v.val = u.val + d →
        S.sortedRows u = S.sortedRows v → S.shuffleGraph.Reachable u v := by
      intro d
      induction d with
      | zero =>
        intro u v hv _
        have he : u = v := Fin.ext (by omega)
        subst v
        exact SimpleGraph.Reachable.refl u
      | succ d ih =>
        intro u v hv huv
        let w : Fin N := ⟨v.val - 1, by omega⟩
        have huw : u ≤ w := by change u.val ≤ v.val - 1; omega
        have hwv : w ≤ v := by change v.val - 1 ≤ v.val; omega
        have hw : S.sortedRows w = S.sortedRows u := S.equal_rows_between huw hwv huv
        have hdist : w.val = u.val + d := by change v.val - 1 = u.val + d; omega
        have hadj : S.shuffleGraph.Adj w v :=
          ⟨Or.inl (by change v.val - 1 + 1 = v.val; omega), hw.trans huv⟩
        exact (ih u w hdist hw.symm).trans hadj.reachable
    rcases le_total i j with hij | hji
    · exact forward (j.val - i.val) i j (by omega) heq
    · exact (forward (i.val - j.val) j i (by omega) heq.symm).symm

/-- G06. -/
theorem block_adj_iff (S : ShuffleMatrix P) (x : Node P) (i j : Fin N) :
    (S.blockGraph x).Adj i j ↔ S.shuffleGraph.Adj i j ∧ i ∈ S.rankSet x ∧ j ∈ S.rankSet x :=
  Iff.rfl

/-- G07. -/
theorem shared_adj_iff (S T : ShuffleMatrix P) (i j : Fin N) :
    (S.sharedGraph T).Adj i j ↔ S.shuffleGraph.Adj i j ∧ T.shuffleGraph.Adj i j :=
  Iff.rfl

end ShuffleMatrix
end RiffleShuffle
