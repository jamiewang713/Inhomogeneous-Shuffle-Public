import RiffleUpperV2.Localization.EdgeRanks

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Localization

/-- Full-word sorted positions are exactly the global deterministic rank interval. -/
theorem sortedWord_rank_iff {k n d : ℕ} {cuts : Cuts k n d} (ω : Sample cuts)
    (w : Word k d) (i : Fin n) :
    sortedWord ω i=w ↔ wordLower Finset.univ w ω ≤ i.val ∧
      i.val < wordLower Finset.univ w ω+restrictedWordCount Finset.univ w ω := by
  have h := RiffleLowerV2.Model.prefixRanks cuts ω (RiffleLowerV2.fullPrefix w)
  have hl : lowerRank (RiffleLowerV2.fullPrefix w) ω=wordLower Finset.univ w ω := by
    unfold RiffleUpperV2.lowerRank RiffleLowerV2.lowerRank RiffleLowerV2.fullPrefix wordLower
    simp only [Fin.val_last,List.take_of_length_le (show (rowWord ω _).toList.length ≤ d by simp)]
  have hc : prefixCount (RiffleLowerV2.fullPrefix w) ω=restrictedWordCount Finset.univ w ω := by
    unfold RiffleUpperV2.prefixCount RiffleLowerV2.prefixCount RiffleLowerV2.fullPrefix restrictedWordCount
    congr 1
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_last]
    rw [List.take_of_length_le (by simp)]
    exact List.Vector.toList_injective.eq_iff
  have hlu : lowerRank (RiffleLowerV2.fullPrefix w) ω ≤ upperRank (RiffleLowerV2.fullPrefix w) ω := by
    apply Finset.card_le_card
    intro r hr
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1,(Finset.mem_filter.mp hr).2.le⟩
  have hu : upperRank (RiffleLowerV2.fullPrefix w) ω=
      wordLower Finset.univ w ω+restrictedWordCount Finset.univ w ω := by
    have hp := h.2
    change upperRank (RiffleLowerV2.fullPrefix w) ω-lowerRank (RiffleLowerV2.fullPrefix w) ω = prefixCount (RiffleLowerV2.fullPrefix w) ω at hp
    rw [hl,hc] at hp
    rw [hl] at hlu
    omega
  have hi := h.1 i
  change (sortedWord ω i).toList.take d=w.toList ↔ lowerRank (RiffleLowerV2.fullPrefix w) ω ≤ i.val ∧ i.val < upperRank (RiffleLowerV2.fullPrefix w) ω at hi
  rw [List.take_of_length_le (by simp),hl,hu] at hi
  exact (show sortedWord ω i=w ↔ (sortedWord ω i).toList=w.toList from
    ⟨fun hh => congrArg List.Vector.toList hh,fun hh => List.Vector.toList_injective hh⟩).trans hi

/-- Literal zero-based edge ranks in the globally sorted shuffle graph. -/
theorem shuffleEdges_mem_word {k n d : ℕ} {cuts : Cuts k n d} (ω : Sample cuts)
    (e : Fin (n-1)) :
    e ∈ shuffleEdges ω ↔ ∃ w : Word k d, (e.val : ℤ) ∈ wordEdgeInterval 0 Finset.univ w ω := by
  simp only [RiffleUpperV2.shuffleEdges,RiffleLowerV2.shuffleEdges,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · intro he
    let w := sortedWord ω (RiffleLowerV2.edgeLeft e)
    have hl := (sortedWord_rank_iff ω w (RiffleLowerV2.edgeLeft e)).mp rfl
    have hu := (sortedWord_rank_iff ω w (RiffleLowerV2.edgeRight e)).mp he.symm
    refine ⟨w,Finset.mem_Ico.mpr ?_⟩
    dsimp [RiffleLowerV2.edgeLeft,RiffleLowerV2.edgeRight] at hl hu
    constructor <;> omega
  · rintro ⟨w,hw⟩
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hw
    have he1 : sortedWord ω (RiffleLowerV2.edgeLeft e)=w := by
      apply (sortedWord_rank_iff ω w _).mpr
      dsimp [RiffleLowerV2.edgeLeft]
      constructor <;> omega
    have he2 : sortedWord ω (RiffleLowerV2.edgeRight e)=w := by
      apply (sortedWord_rank_iff ω w _).mpr
      dsimp [RiffleLowerV2.edgeRight]
      constructor <;> omega
    exact he1.trans he2.symm

end RiffleUpperV2.Localization
