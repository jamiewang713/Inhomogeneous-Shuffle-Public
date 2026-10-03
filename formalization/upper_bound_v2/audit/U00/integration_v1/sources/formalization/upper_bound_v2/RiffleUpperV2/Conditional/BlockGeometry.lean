import RiffleUpperV2.Reservoir.FutureGraphLaw
import RiffleUpperV2.Conditional.FutureCylinders

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Reservoir TimeProfile

/-- The occupied cylinder occupies exactly its actual absolute rank interval. -/
theorem cylinderRank_card {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K) (ω : Sample cuts) :
    upperRank x ω = lowerRank x ω+(cylinderRows x ω).card ∧ upperRank x ω ≤ n := by
  have h := (RiffleLowerV2.Model.prefixRanks cuts ω x).2
  have hle : lowerRank x ω ≤ upperRank x ω := by
    apply Finset.card_le_card
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2.le⟩
  have hu : upperRank x ω ≤ n := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin _))
  have hc : (cylinderRows x ω).card = prefixCount x ω := rfl
  exact ⟨by simp only [lowerRank,upperRank,prefixCount] at *; omega,hu⟩

def cylinderPosition {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K) (ω : Sample cuts)
    (i : Fin (cylinderRows x ω).card) : Fin n :=
  ⟨lowerRank x ω+i.val,by have := cylinderRank_card cuts x ω; have := i.isLt; omega⟩

theorem cylinderPosition_mem {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K)
    (ω : Sample cuts) (i : Fin (cylinderRows x ω).card) :
    RiffleLowerV2.stableSort ω (cylinderPosition cuts x ω i) ∈ cylinderRows x ω := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  apply (RiffleLowerV2.Model.prefixRanks cuts ω x).1 _ |>.mpr
  have := cylinderRank_card cuts x ω
  have := i.isLt
  dsimp [cylinderPosition]
  simp only [lowerRank,upperRank] at *
  omega

def sortedCylinderEquiv {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K) (ω : Sample cuts) :
    Fin (cylinderRows x ω).card ≃ ↥(cylinderRows x ω) where
  toFun i := ⟨RiffleLowerV2.stableSort ω (cylinderPosition cuts x ω i),cylinderPosition_mem cuts x ω i⟩
  invFun r := ⟨((RiffleLowerV2.stableSort ω).symm r.val).val-lowerRank x ω,by
    have hp := (RiffleLowerV2.Model.prefixRanks cuts ω x).1 ((RiffleLowerV2.stableSort ω).symm r.val)
    have hpre : (sortedWord ω ((RiffleLowerV2.stableSort ω).symm r.val)).toList.take x.1.val=x.2.toList := by
      simpa only [RiffleLowerV2.sortedWord,Equiv.apply_symm_apply] using (Finset.mem_filter.mp r.property).2
    have hr := hp.mp hpre
    have hc := cylinderRank_card cuts x ω
    simp only [lowerRank,upperRank] at *
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp [cylinderPosition]
  right_inv r := by
    apply Subtype.ext
    have hp := (RiffleLowerV2.Model.prefixRanks cuts ω x).1 ((RiffleLowerV2.stableSort ω).symm r.val)
    have hpre : (sortedWord ω ((RiffleLowerV2.stableSort ω).symm r.val)).toList.take x.1.val=x.2.toList := by
      simpa only [RiffleLowerV2.sortedWord,Equiv.apply_symm_apply] using (Finset.mem_filter.mp r.property).2
    have hr := hp.mp hpre
    have he : cylinderPosition cuts x ω
        ⟨((RiffleLowerV2.stableSort ω).symm r.val).val-lowerRank x ω,by
          have hc := cylinderRank_card cuts x ω; simp only [lowerRank,upperRank] at *; omega⟩ = (RiffleLowerV2.stableSort ω).symm r.val := by
      apply Fin.ext
      dsimp [cylinderPosition]
      simp only [lowerRank] at *
      omega
    exact (congrArg (RiffleLowerV2.stableSort ω) he).trans
      ((RiffleLowerV2.stableSort ω).apply_symm_apply r.val)

/-- Sorting the actual labeled cylinder gives the same word at local i as
whole-matrix sorting at lowerRank+i, regardless of the label enumeration. -/
theorem sortedBlockWord_eq {k n K : ℕ} (cuts : Cuts k n K) (x : Prefix k K) (ω : Sample cuts)
    (i : Fin (cylinderRows x ω).card) :
    (blockWords (cylinderRows x ω) ω ∘ Tuple.sort (blockWords (cylinderRows x ω) ω)) i =
      sortedWord ω (cylinderPosition cuts x ω i) := by
  let σ := (sortedCylinderEquiv cuts x ω).trans (cylinderRows x ω).equivFin
  have he (j : Fin (cylinderRows x ω).card) :
      blockWords (cylinderRows x ω) ω (σ j)=sortedWord ω (cylinderPosition cuts x ω j) := by
    simp [blockWords,σ,sortedCylinderEquiv,RiffleLowerV2.sortedWord]
  have hm : Monotone (blockWords (cylinderRows x ω) ω ∘ σ) := by
    intro a b hab
    simp only [Function.comp_apply,he]
    apply Tuple.monotone_sort (rowWord ω)
    change lowerRank x ω+a.val ≤ lowerRank x ω+b.val
    exact Nat.add_le_add_left hab _
  have hs := Tuple.comp_sort_eq_comp_iff_monotone.mpr hm
  exact (congrFun hs i).symm.trans (he i)

end RiffleUpperV2.Conditional
