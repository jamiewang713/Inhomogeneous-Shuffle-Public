import RiffleUpperV2.Exploration.DirectionalRanks
import RiffleUpperV2.Exploration.DirectionalGuards
import RiffleUpperV2.Exploration.Processes

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration

/-- At the same spatial location, two H-matrices have a common direction. -/
theorem commonDirection_on_concentration {k n L : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0 < n) (hk : 1 ≤ k) (D : ℕ) {g ξ : ℝ} (hg : 0 < g)
    (hc : retainedGoodCluster cuts hn D g) (p : Fin k)
    (hp : (n : ℝ)^ξ ≤ pileSize cuts p) {ω ω' : Sample cuts}
    (h : concentrationEvent cuts D g ξ ω) (h' : concentrationEvent cuts D g ξ ω')
    (r : Fin (pileSize cuts p)) :
    (hasDirection cuts D g .forward (sortedWord ω (pilePosition cuts p .forward r)) ∧
      hasDirection cuts D g .forward (sortedWord ω' (pilePosition cuts p .forward r))) ∨
    (hasDirection cuts D g .backward (sortedWord ω (pilePosition cuts p .forward r)) ∧
      hasDirection cuts D g .backward (sortedWord ω' (pilePosition cuts p .forward r))) := by
  obtain ⟨v,hv⟩ := chosenReserves_of_retainedGoodCluster cuts hn hk D hg.le hc
  simp only [hasDirection, hv]
  have hcross (a b : Sample cuts) (ha : concentrationEvent cuts D g ξ a)
      (hb : concentrationEvent cuts D g ξ b)
      (hl : tailPrefix D (sortedWord a (pilePosition cuts p .forward r)) < v.2.1)
      (hr : v.2.1 < tailPrefix D (sortedWord b (pilePosition cuts p .forward r))) : False := by
    have hleft := (guard_before_rank cuts D g p a v hv r).mpr hl
    have hright : ¬ r.val < guardCount cuts D g p true b := by
      intro hh
      exact (not_le_of_gt hr) ((guard_through_rank cuts D g p b v hv r).mp hh)
    have hsep := guards_interlace_on_concentration cuts hn hk D hg hc p hp ha hb
    omega
  by_cases hf : tailPrefix D (sortedWord ω (pilePosition cuts p .forward r)) ≤ v.2.1 ∧
      tailPrefix D (sortedWord ω' (pilePosition cuts p .forward r)) ≤ v.2.1
  · exact Or.inl hf
  · right
    constructor
    · by_contra hh
      have hl := lt_of_not_ge hh
      have hr : v.2.1 < tailPrefix D (sortedWord ω' (pilePosition cuts p .forward r)) := by
        by_contra hhr
        exact hf ⟨hl.le,le_of_not_gt hhr⟩
      exact hcross ω ω' h h' hl hr
    · by_contra hh
      have hl := lt_of_not_ge hh
      have hr : v.2.1 < tailPrefix D (sortedWord ω (pilePosition cuts p .forward r)) := by
        by_contra hhr
        exact hf ⟨le_of_not_gt hhr,hl.le⟩
      exact hcross ω' ω h' h hl hr

/-- Spatial reversal of an edge; word coordinates are not reversed. -/
def reversePileEdge {m : ℕ} (e : Fin (m-1)) : Fin (m-1) :=
  ⟨m-2-e.val, by omega⟩

@[simp] theorem reversePileEdge_involutive {m : ℕ} (e : Fin (m-1)) :
    reversePileEdge (reversePileEdge e) = e := by
  apply Fin.ext
  simp only [reversePileEdge]
  omega

theorem directionalEdge_backward_iff {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g : ℝ) (p : Fin k) (e : Fin (pileSize cuts p-1)) (ω : Sample cuts) :
    directionalEdge cuts D g p .backward (reversePileEdge e) ω ↔
      sortedWord ω (pilePosition cuts p .forward ⟨e.val,by omega⟩) =
        sortedWord ω (pilePosition cuts p .forward ⟨e.val+1,by omega⟩) ∧
      hasDirection cuts D g .backward (sortedWord ω (pilePosition cuts p .forward ⟨e.val,by omega⟩)) := by
  have hleft : pilePosition cuts p .backward ⟨(reversePileEdge e).val,by have := (reversePileEdge e).isLt; omega⟩ =
      pilePosition cuts p .forward ⟨e.val+1,by omega⟩ := by
    apply Fin.ext
    simp only [pilePosition, spatialIndex, reversePileEdge]
    omega
  have hright : pilePosition cuts p .backward ⟨(reversePileEdge e).val+1,by have := (reversePileEdge e).isLt; omega⟩ =
      pilePosition cuts p .forward ⟨e.val,by omega⟩ := by
    apply Fin.ext
    simp only [pilePosition, spatialIndex, reversePileEdge]
    omega
  dsimp only [directionalEdge]
  rw [hleft,hright]
  constructor
  · rintro ⟨he,hd⟩
    exact ⟨he.symm,he ▸ hd⟩
  · rintro ⟨he,hd⟩
    exact ⟨he.symm,he ▸ hd⟩

/-- Every common within-pile edge in a large pile lies in a common direction on H×H. -/
theorem directionalCover {k n L : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0 < n) (hk : 1 ≤ k) (D : ℕ) {g ξ : ℝ} (hg : 0 < g)
    (hc : retainedGoodCluster cuts hn D g) (p : Fin k)
    (hp : (n : ℝ)^ξ ≤ pileSize cuts p) {ω ω' : Sample cuts}
    (h : concentrationEvent cuts D g ξ ω) (h' : concentrationEvent cuts D g ξ ω')
    (e : Fin (pileSize cuts p-1))
    (he : sortedWord ω (pilePosition cuts p .forward ⟨e.val,by omega⟩) =
      sortedWord ω (pilePosition cuts p .forward ⟨e.val+1,by omega⟩))
    (he' : sortedWord ω' (pilePosition cuts p .forward ⟨e.val,by omega⟩) =
      sortedWord ω' (pilePosition cuts p .forward ⟨e.val+1,by omega⟩)) :
    (directionalEdge cuts D g p .forward e ω ∧ directionalEdge cuts D g p .forward e ω') ∨
      (directionalEdge cuts D g p .backward (reversePileEdge e) ω ∧
        directionalEdge cuts D g p .backward (reversePileEdge e) ω') := by
  rcases commonDirection_on_concentration cuts hn hk D hg hc p hp h h' ⟨e.val,by omega⟩ with hf | hb
  · exact Or.inl ⟨⟨he,hf.1⟩,⟨he',hf.2⟩⟩
  · right
    exact ⟨(directionalEdge_backward_iff cuts D g p e ω).mpr ⟨he,hb.1⟩,
      (directionalEdge_backward_iff cuts D g p e ω').mpr ⟨he',hb.2⟩⟩

end RiffleUpperV2.Exploration
