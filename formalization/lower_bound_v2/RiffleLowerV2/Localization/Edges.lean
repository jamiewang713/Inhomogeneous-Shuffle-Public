import RiffleLowerV2.Model.Sorting

noncomputable section
namespace RiffleLowerV2.Localization
attribute [local instance] Classical.propDecidable

theorem prefix_rank_bounds {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (omega : Sample cuts) (w : Prefix k K) :
    lowerRank w omega ≤ upperRank w omega ∧ upperRank w omega ≤ N := by
  constructor
  · apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin N)

theorem sortedWord_full_rank_iff {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (omega : Sample cuts) (w : Word k K) (i : Fin N) :
    sortedWord omega i = w ↔
      lowerRank (fullPrefix w) omega ≤ i.val ∧ i.val < upperRank (fullPrefix w) omega := by
  have h := (Model.prefixRanks cuts omega (fullPrefix w)).1 i
  have ht : (sortedWord omega i).toList.take K = (sortedWord omega i).toList := by
    simpa only [List.Vector.toList_length] using (List.take_length (l := (sortedWord omega i).toList))
  simp only [fullPrefix, Fin.val_last, ht] at h
  constructor
  · intro he
    exact h.mp (congrArg List.Vector.toList he)
  · intro hi
    exact Subtype.ext (h.mpr hi)

/-- The left index of the edge joining a complete word's first two copies. -/
def firstRepeatedWordEdge {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (omega : Sample cuts) (w : Word k K) (hw : 2 ≤ wordCount w omega) : Fin (N-1) :=
  ⟨lowerRank (fullPrefix w) omega, by
    have hb := prefix_rank_bounds omega (fullPrefix w)
    have hc := (Model.prefixRanks cuts omega (fullPrefix w)).2
    change upperRank (fullPrefix w) omega-lowerRank (fullPrefix w) omega = wordCount w omega at hc
    omega⟩

theorem firstRepeatedWordEdge_words {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (omega : Sample cuts) (w : Word k K) (hw : 2 ≤ wordCount w omega) :
    sortedWord omega (edgeLeft (firstRepeatedWordEdge omega w hw)) = w ∧
    sortedWord omega (edgeRight (firstRepeatedWordEdge omega w hw)) = w := by
  have hb := prefix_rank_bounds omega (fullPrefix w)
  have hc := (Model.prefixRanks cuts omega (fullPrefix w)).2
  change upperRank (fullPrefix w) omega-lowerRank (fullPrefix w) omega = wordCount w omega at hc
  constructor <;> apply (sortedWord_full_rank_iff omega w _).mpr
  · change lowerRank (fullPrefix w) omega ≤ lowerRank (fullPrefix w) omega ∧
      lowerRank (fullPrefix w) omega < upperRank (fullPrefix w) omega
    omega
  · change lowerRank (fullPrefix w) omega ≤ lowerRank (fullPrefix w) omega+1 ∧
      lowerRank (fullPrefix w) omega+1 < upperRank (fullPrefix w) omega
    omega

theorem firstRepeatedWordEdge_injective {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (omega : Sample cuts) :
    Function.Injective (fun w : {w : Word k K // 2 ≤ wordCount w omega} =>
      firstRepeatedWordEdge omega w.val w.property) := by
  intro w v he
  dsimp only at he
  apply Subtype.ext
  have hw := (firstRepeatedWordEdge_words omega w.val w.property).1
  have hv := (firstRepeatedWordEdge_words omega v.val v.property).1
  rw [he] at hw
  exact hw.symm.trans hv

/-- Repeated words yield an explicit injective map to actual internal shuffle edges. -/
theorem localized_collisions_supply_edges {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (omega : Sample cuts) (Y : Finset (Word k K)) (H : Finset (Fin N))
    (hloc : ∀ y ∈ Y, ∀ i : Fin N, sortedWord omega i = y → i ∈ H) :
    ((Y.filter fun y => 2 ≤ wordCount y omega).card ≤
      ((shuffleEdges omega) ∩ internalEdges H).card) := by
  let A := Y.filter fun y => 2 ≤ wordCount y omega
  let edge (w : A) : Fin (N-1) :=
    firstRepeatedWordEdge omega w.val (Finset.mem_filter.mp w.property).2
  have hmem (w : A) : edge w ∈ shuffleEdges omega ∩ internalEdges H := by
    have hwY := (Finset.mem_filter.mp w.property).1
    have hwords := firstRepeatedWordEdge_words omega w.val (Finset.mem_filter.mp w.property).2
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwords.1.trans hwords.2.symm⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨hloc w.val hwY _ hwords.1, hloc w.val hwY _ hwords.2⟩
  let assignment : A → {e : Fin (N-1) // e ∈ shuffleEdges omega ∩ internalEdges H} :=
    fun w => ⟨edge w, hmem w⟩
  have hinj : Function.Injective assignment := by
    intro w v he
    apply Subtype.ext
    have hedges : edge w = edge v := congrArg Subtype.val he
    have hw := (firstRepeatedWordEdge_words omega w.val (Finset.mem_filter.mp w.property).2).1
    have hv := (firstRepeatedWordEdge_words omega v.val (Finset.mem_filter.mp v.property).2).1
    change sortedWord omega (edgeLeft (edge w)) = w.val at hw
    change sortedWord omega (edgeLeft (edge v)) = v.val at hv
    rw [hedges] at hw
    exact hw.symm.trans hv
  simpa only [Fintype.card_coe, A] using Fintype.card_le_of_injective assignment hinj

end RiffleLowerV2.Localization
