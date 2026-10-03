import RiffleUpperV2.GraphOverlap.Fibers

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.GraphOverlap
open RiffleLowerV2 RiffleLowerV2.Model
variable {N : ℕ}

theorem componentIndex_edge_eq_iff (G : PathEdges N) (e : Fin (N-1)) :
    componentIndex G (edgeLeft e) = componentIndex G (edgeRight e) ↔ e ∈ G := by
  constructor
  · intro h
    by_contra hn
    exact (ne_of_lt (componentIndex_lt_of_missing G e hn)) h
  · intro he
    unfold componentIndex
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ha, hm⟩
      exact ⟨by dsimp [edgeLeft, edgeRight] at *; omega, hm⟩
    · rintro ⟨ha, hm⟩
      refine ⟨?_, hm⟩
      have hne : a ≠ e := by intro h; exact hm (h ▸ he)
      have : a.val ≠ e.val := fun h => hne (Fin.ext h)
      dsimp [edgeLeft, edgeRight] at *
      omega

/-- The component support is equivalently increase across every present edge. -/
theorem blockIncreasing_iff_edges (G : PathEdges N) (σ : Permutation N) :
    BlockIncreasing G σ ↔ ∀ e ∈ G, σ (edgeLeft e) < σ (edgeRight e) := by
  constructor
  · intro h e he
    exact h _ _ (by simp [edgeLeft, edgeRight])
      ((componentIndex_edge_eq_iff G e).mpr he)
  · intro h
    have aux : ∀ d : ℕ, ∀ a b : Fin N, b.val - a.val = d → a < b →
        componentIndex G a = componentIndex G b → σ a < σ b := by
      intro d
      induction d with
      | zero => intro a b hd hab; have : a.val < b.val := hab; omega
      | succ d ih =>
        intro a b hd hab hc
        let q : Fin N := ⟨b.val-1, by have := b.isLt; omega⟩
        let e : Fin (N-1) := ⟨b.val-1, by have := b.isLt; omega⟩
        have hel : edgeLeft e = q := by apply Fin.ext; rfl
        have her : edgeRight e = b := by apply Fin.ext; dsimp [edgeRight, e]; omega
        have haq : a ≤ q := by change a.val ≤ b.val-1; omega
        have hqb : q ≤ b := by change b.val-1 ≤ b.val; omega
        have hqc : componentIndex G q = componentIndex G b :=
          le_antisymm (componentIndex_monotone _ hqb)
            (hc ▸ componentIndex_monotone _ haq)
        have he : e ∈ G := (componentIndex_edge_eq_iff G e).mp (by simpa [hel, her] using hqc)
        have hlast : σ q < σ b := by simpa [hel, her] using h e he
        rcases haq.eq_or_lt with heq | hlt
        · simpa only [← heq] using hlast
        · exact (ih a q (by dsimp [q]; omega) hlt (hc.trans hqc.symm)).trans hlast
    intro a b hab hc
    exact aux _ a b rfl hab hc

theorem blockIncreasing_union (G H : PathEdges N) (σ : Permutation N) :
    BlockIncreasing (G ∪ H) σ ↔ BlockIncreasing G σ ∧ BlockIncreasing H σ := by
  simp only [blockIncreasing_iff_edges, Finset.mem_union]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

end RiffleUpperV2.GraphOverlap
