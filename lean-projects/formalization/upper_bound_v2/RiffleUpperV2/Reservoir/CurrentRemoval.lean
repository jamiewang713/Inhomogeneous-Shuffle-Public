import RiffleUpperV2.Reservoir.RestrictedPrefix

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

theorem tupleCount_split {k L r : ℕ} (A : Finset (Fin r)) (w : Fin r → Word k L) (u : Word k L) :
    tupleCount w u=selectedWordCount A w u+selectedWordCount (Finset.univ \ A) w u := by
  have hd : Disjoint (A.filter fun q => w q=u) ((Finset.univ \ A).filter fun q => w q=u) := by
    apply Finset.disjoint_left.mpr
    intro q ha hb
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).2 (Finset.mem_filter.mp ha).1
  have he : Finset.univ.filter (fun q => w q=u)=
      (A.filter fun q => w q=u) ∪ ((Finset.univ \ A).filter fun q => w q=u) := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_sdiff]
    tauto
  exact (congrArg Finset.card he).trans (Finset.card_union_of_disjoint hd)

theorem selectedWordCount_of_constant {k L r : ℕ} (A : Finset (Fin r))
    (w : Fin r → Word k L) (s : Word k L) (hs : ∀ q∈A, w q=s) (u : Word k L) :
    selectedWordCount A w u=if s=u then A.card else 0 := by
  by_cases h : s=u
  · subst u
    unfold selectedWordCount
    rw [Finset.filter_eq_self.mpr hs]
    simp
  · unfold selectedWordCount
    rw [Finset.filter_eq_empty_iff.mpr (fun q hq hh => h ((hs q hq).symm.trans hh))]
    simp [h]

/-- A removable terminal copy leaves exactly the history's forced terminal
multiplicity in the unmarked rows; it is not counted as a fresh observed copy. -/
theorem unmarkedHistoryConstraint_of_current_removal {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω : Sample cuts) (j : Fin (pileSize cuts p))
    (A : Finset (Fin (pileSize cuts p))) (a w : Fin (pileSize cuts p) → Word k (L+1))
    (hm : (Finset.univ \ A).card=1) (hfix : ∀ q∈A, w q=a q)
    (hh : tupleHistoryConstraint cuts p ω j w)
    (hs : ∀ q, q∉A → w q=pileWords cuts p ω j)
    (hremove : observedCount (pileWords cuts p ω) (j.val+1) (pileWords cuts p ω j) ≤
      tupleCount w (pileWords cuts p ω j)-1) :
    unmarkedHistoryConstraint cuts p ω j A a := by
  have hconst : ∀ q∈Finset.univ \ A, w q=pileWords cuts p ω j :=
    fun q hq => hs q (Finset.mem_sdiff.mp hq).2
  have hcount (u : Word k (L+1)) : tupleCount w u=selectedWordCount A a u+
      (if pileWords cuts p ω j=u then 1 else 0) := by
    rw [tupleCount_split A w u,selectedWordCount_congr A a w hfix,
      selectedWordCount_of_constant _ w _ hconst,hm]
  refine ⟨?_,?_,?_⟩
  · intro q hq
    rw [← hfix q hq]
    exact hh.1 q
  · intro u hp hu
    have hx := hh.2.1 u hp hu
    rw [hcount u,if_neg (Ne.symm (ne_of_lt hu)),add_zero] at hx
    exact hx
  · rw [hcount _,if_pos rfl] at hremove
    omega

end RiffleUpperV2.Reservoir
