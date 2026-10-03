import RiffleUpperV2.Conditional.BlockEdges
import RiffleUpperV2.Localization.GlobalRanks

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Reservoir RiffleUpperV2.Localization Anchor
attribute [local instance 2000] Reservoir.wordDecEq

/-- A cylinder has at most as many internal edges as labeled rows. -/
theorem absoluteBlockGraph_card_le_count {k n K : ℕ} (cuts : Cuts k n K)
    (x : Prefix k K) (ω : Sample cuts) :
    (absoluteBlockGraph x ω).card≤RiffleUpperV2.prefixCount x ω := by
  have himage := Finset.card_image_le (s := blockGraph (cylinderRows x ω) ω)
    (f := fun e => (lowerRank x ω:ℤ)+e.val)
  have hedge : (blockGraph (cylinderRows x ω) ω).card≤(cylinderRows x ω).card-1 :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  exact himage.trans (hedge.trans (Nat.sub_le _ _))

/-- The local graph's absolute edges are the actual anchored prefix edges. -/
theorem absoluteBlockGraph_subset_anchored {k n K : ℕ} (cuts : Cuts k n K)
    (x : Prefix k K) (ω : Sample cuts) :
    absoluteBlockGraph x ω⊆anchoredEdges 0 Finset.univ x ω := by
  intro z hz
  obtain ⟨e,he,rfl,_,_⟩ := (absoluteBlockGraph_mem_iff cuts x ω z).mp hz
  let w := sortedWord ω (RiffleLowerV2.edgeLeft e)
  have hw := (absoluteBlockGraph_edge_iff cuts x ω e he).mp hz
  have heq : sortedWord ω (RiffleLowerV2.edgeLeft e)=sortedWord ω (RiffleLowerV2.edgeRight e) := by
    simpa only [shuffleEdges,RiffleLowerV2.shuffleEdges,Finset.mem_filter,Finset.mem_univ,true_and] using he
  have hl := (sortedWord_rank_iff ω w (RiffleLowerV2.edgeLeft e)).mp rfl
  have hr := (sortedWord_rank_iff ω w (RiffleLowerV2.edgeRight e)).mp heq.symm
  apply (anchoredEdges_mem_word 0 Finset.univ x ω _).mpr
  refine ⟨w,?_,Finset.mem_Ico.mpr ?_⟩
  · simpa only [List.Vector.toList_length] using (List.prefix_iff_eq_take.mp hw).symm
  · dsimp [RiffleLowerV2.edgeLeft,RiffleLowerV2.edgeRight] at hl hr
    constructor <;> omega

/-- Intermediate cylinders use full-word collision pairs, with no factor
counting the number of possible terminal words. -/
theorem absoluteBlockGraph_card_le_collisions {k n K : ℕ} (cuts : Cuts k n K)
    (x : Prefix k K) (ω : Sample cuts) :
    ((absoluteBlockGraph x ω).card:ℝ)≤∑w:Word k K,
      if w.toList.take x.1.val=x.2.toList then ((wordCount ω w).choose 2:ℝ) else 0 := by
  have hs : ((absoluteBlockGraph x ω).card:ℝ)≤((anchoredEdges 0 Finset.univ x ω).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (absoluteBlockGraph_subset_anchored cuts x ω)
  rw [anchoredEdges_card] at hs
  apply hs.trans ((internalOffsets_card_le_pairs (internalHistory Finset.univ x ω)).trans_eq ?_)
  apply Finset.sum_congr rfl
  intro w _
  rw [historyWordRows_internal]
  split_ifs with hw
  · congr 2
    apply congrArg Finset.card
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  · simp

end RiffleUpperV2.Conditional
