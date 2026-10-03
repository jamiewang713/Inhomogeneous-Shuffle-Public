import RiffleUpperV2.Localization.CollisionMass
import RiffleUpperV2.Localization.IntervalInclusion

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

def wordLower {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (w : Word k d) (ω : Sample cuts) : ℕ :=
  (R.filter (fun r => (rowWord ω r).toList < w.toList)).card

def wordEdgeInterval {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ) (R : Finset (Fin n))
    (w : Word k d) (ω : Sample cuts) : Finset ℤ :=
  Finset.Ico (c₀+wordLower R w ω) (c₀+wordLower R w ω+restrictedWordCount R w ω-1)

theorem historyLessRows_internal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) (w : Word k d) :
    historyLessRows (internalHistory R x ω) w.get =
      (prefixRows R x ω).filter (fun r => (rowWord ω r).toList<w.toList) := by
  have hw : List.ofFn w.get=w.toList := by
    simpa only [List.Vector.toList_ofFn] using congrArg List.Vector.toList (List.Vector.ofFn_get w)
  ext r
  have hrow : (rowWord ω r).toList=List.ofFn (fun j => TimeProfile.sampleEntry ω r j) := by
    rw [← List.Vector.toList_ofFn]
    apply congrArg List.Vector.toList
    apply List.Vector.ext
    intro j
    exact (RiffleLowerV2.rowWord_get ω r j).trans (List.Vector.get_ofFn _ j).symm
  simp only [historyLessRows,Finset.mem_filter,Finset.mem_univ,true_and,internalHistory,hw,hrow]
  by_cases hr : r ∈ prefixRows R x ω
  · simp only [hr,if_true,Option.some.injEq,true_and]
    constructor
    · rintro ⟨q,hq,hlt⟩
      subst q
      exact hlt
    · intro h
      refine ⟨_,rfl,?_⟩
      exact h
  · simp [hr]

theorem prefixLower_add_internalLess {k n d : ℕ} {cuts : Cuts k n d}
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) (w : Word k d)
    (hw : w.toList.take x.1.val=x.2.toList) :
    lowerEndpoint c₀ R x ω+(historyLessRows (internalHistory R x ω) w.get).card =
      c₀+wordLower R w ω := by
  rw [historyLessRows_internal]
  have hu : (R.filter (fun r => (rowWord ω r).toList.take x.1.val < x.2.toList)) ∪
      ((prefixRows R x ω).filter (fun r => (rowWord ω r).toList<w.toList)) =
      R.filter (fun r => (rowWord ω r).toList<w.toList) := by
    ext r
    simp only [Finset.mem_union,Finset.mem_filter,prefixRows]
    constructor
    · rintro (⟨hr,hlt⟩ | ⟨⟨hr,heq⟩,hlt⟩)
      · refine ⟨hr,?_⟩
        by_contra hno
        have hm := RiffleShuffle.take_lex_monotone x.1.val (le_of_not_gt hno)
        rw [hw] at hm
        exact not_lt_of_ge hm hlt
      · exact ⟨hr,hlt⟩
    · rintro ⟨hr,hlt⟩
      have hm := RiffleShuffle.take_lex_monotone x.1.val hlt.le
      rw [hw] at hm
      rcases lt_or_eq_of_le hm with h | h
      · exact Or.inl ⟨hr,h⟩
      · exact Or.inr ⟨⟨hr,h⟩,hlt⟩
  have hd : Disjoint (R.filter (fun r => (rowWord ω r).toList.take x.1.val < x.2.toList))
      ((prefixRows R x ω).filter (fun r => (rowWord ω r).toList<w.toList)) := by
    apply Finset.disjoint_left.mpr
    intro r ha hb
    have hlt := (Finset.mem_filter.mp ha).2
    have heq := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    exact hlt.ne heq
  have hc := Finset.card_union_of_disjoint hd
  rw [hu] at hc
  unfold lowerEndpoint wordLower
  push_cast at hc ⊢
  omega

theorem anchoredEdges_mem_word {k n d : ℕ} {cuts : Cuts k n d}
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) (m : ℤ) :
    m ∈ anchoredEdges c₀ R x ω ↔ ∃ w : Word k d,
      w.toList.take x.1.val=x.2.toList ∧ m ∈ wordEdgeInterval c₀ R w ω := by
  constructor
  · intro hm
    obtain ⟨j,hj,hjm⟩ := Finset.mem_image.mp hm
    obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hj
    let w : Word k d := List.Vector.ofFn q
    have hwget : w.get=q := by funext i; simp [w]
    have hq' : j ∈ Finset.Ico ((historyLessRows (internalHistory R x ω) w.get).card : ℤ)
      ((historyLessRows (internalHistory R x ω) w.get).card+
       (historyWordRows (internalHistory R x ω) w.get).card-1) := by simpa only [hwget] using hq
    have hw : w.toList.take x.1.val=x.2.toList := by
      by_contra hno
      rw [historyWordRows_internal,if_neg hno] at hq'
      simp only [Finset.card_empty,Nat.cast_zero,add_zero,Finset.mem_Ico] at hq'
      omega
    refine ⟨w,hw,?_⟩
    have he := prefixLower_add_internalLess c₀ R x ω w hw
    rw [historyWordRows_internal,if_pos hw] at hq'
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hq'
    apply Finset.mem_Ico.mpr
    unfold restrictedWordCount at *
    omega
  · rintro ⟨w,hw,hm⟩
    refine Finset.mem_image.mpr ⟨m-lowerEndpoint c₀ R x ω,?_,by omega⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨w.get,Finset.mem_univ _,?_⟩
    rw [historyWordRows_internal,if_pos hw]
    have he := prefixLower_add_internalLess c₀ R x ω w hw
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hm
    apply Finset.mem_Ico.mpr
    unfold restrictedWordCount at *
    omega

end RiffleUpperV2.Localization
