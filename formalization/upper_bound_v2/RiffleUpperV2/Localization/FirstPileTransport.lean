import RiffleUpperV2.Localization.GlobalRanks
import RiffleUpperV2.FirstMoment.FirstColumn

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open TimeProfile Anchor Hypergeometric FirstMoment

/-- The future prefix of length zero is the whole exposed first-column pile. -/
def emptyPrefix (k d : ℕ) : Prefix k d := ⟨⟨0,by omega⟩,List.Vector.nil⟩

theorem rowWord_first_tail {k n d : ℕ} {cuts : Cuts k n (d+1)}
    (ω : Sample cuts) (r : Fin n) :
    rowWord ω r=List.Vector.cons ((ω 0).val r) (rowWord (tailSample ω) r) := by
  apply List.Vector.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [RiffleLowerV2.rowWord_get,List.Vector.get_cons_zero,sampleEntry]
  · simp only [RiffleLowerV2.rowWord_get,List.Vector.get_cons_succ,sampleEntry,tailSample]

theorem list_cons_lt_iff {k : ℕ} (a b : Fin k) (u v : List (Fin k)) :
    a::u < b::v ↔ a<b ∨ a=b ∧ u<v := by
  constructor
  · intro h
    cases h with
    | rel h => exact Or.inl h
    | cons h => exact Or.inr ⟨rfl,h⟩
  · rintro (h | ⟨rfl,h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

theorem firstPileStart_count {k n d : ℕ} (cuts : Cuts k n (d+1))
    (ω : Sample cuts) (a : Fin k) :
    firstPileStart cuts a = ((Finset.univ.filter (fun r : Fin n => (ω 0).val r<a)).card : ℤ) := by
  let B := Finset.univ.filter (fun b : Fin k => b<a)
  have hu : B.biUnion (fun b => anchorRows (ω 0) b)=
      Finset.univ.filter (fun r : Fin n => (ω 0).val r<a) := by
    ext r
    simp only [Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and,anchorRows,B]
    constructor
    · rintro ⟨b,hb,hr⟩
      exact hr ▸ hb
    · intro hr
      exact ⟨(ω 0).val r,hr,rfl⟩
  have hd : Set.Pairwise (↑B) (fun a b => Disjoint (anchorRows (ω 0) a) (anchorRows (ω 0) b)) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro r hr hs
    exact hbc ((Finset.mem_filter.mp hr).2.symm.trans (Finset.mem_filter.mp hs).2)
  have hc := Finset.card_biUnion hd
  rw [hu] at hc
  have hci := congrArg (fun q : ℕ => (q:ℤ)) hc
  rw [Nat.cast_sum] at hci
  simp_rw [anchorRows_card] at hci
  exact hci.symm

theorem firstPile_wordLower {k n d : ℕ} (cuts : Cuts k n (d+1))
    (ω : Sample cuts) (a : Fin k) (w : Word k d) :
    firstPileStart cuts a + (wordLower (anchorRows (ω 0) a) w (tailSample ω) : ℤ) =
      wordLower Finset.univ (List.Vector.cons a w) ω := by
  have hu : (Finset.univ.filter (fun r : Fin n => (ω 0).val r<a)) ∪
      ((anchorRows (ω 0) a).filter (fun r => (rowWord (tailSample ω) r).toList<w.toList)) =
      Finset.univ.filter (fun r => (rowWord ω r).toList<(List.Vector.cons a w).toList) := by
    ext r
    simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,anchorRows,
      rowWord_first_tail,List.Vector.toList_cons,list_cons_lt_iff]
  have hd : Disjoint (Finset.univ.filter (fun r : Fin n => (ω 0).val r<a))
      ((anchorRows (ω 0) a).filter (fun r => (rowWord (tailSample ω) r).toList<w.toList)) := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    exact (Finset.mem_filter.mp hr).2.ne (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
  have hc := Finset.card_union_of_disjoint hd
  rw [hu] at hc
  rw [firstPileStart_count]
  unfold wordLower
  exact_mod_cast hc.symm

theorem firstPile_wordCount {k n d : ℕ} (cuts : Cuts k n (d+1))
    (ω : Sample cuts) (a : Fin k) (w : Word k d) :
    restrictedWordCount (anchorRows (ω 0) a) w (tailSample ω) =
      restrictedWordCount Finset.univ (List.Vector.cons a w) ω := by
  unfold restrictedWordCount
  congr 1
  ext r
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,anchorRows,rowWord_first_tail,
    ]
  constructor
  · rintro ⟨ha,h⟩
    simp only [ha,h]
  · intro h
    exact ⟨by simpa using congrArg List.Vector.head h,by simpa using congrArg List.Vector.tail h⟩

theorem firstPile_wordInterval {k n d : ℕ} (cuts : Cuts k n (d+1))
    (ω : Sample cuts) (a : Fin k) (w : Word k d) :
    wordEdgeInterval (firstPileStart cuts a) (anchorRows (ω 0) a) w (tailSample ω) =
      wordEdgeInterval 0 Finset.univ (List.Vector.cons a w) ω := by
  unfold wordEdgeInterval
  rw [firstPile_wordLower,firstPile_wordCount,zero_add]

theorem firstPileEdges_mem_word {k n d : ℕ} (cuts : Cuts k n (d+1))
    (ω : Sample cuts) (a : Fin k) (x : Prefix k d) (m : ℤ) :
    m ∈ firstPileEdges a x ω ↔ ∃ w : Word k d,
      w.toList.take x.1.val=x.2.toList ∧ m ∈ wordEdgeInterval 0 Finset.univ (List.Vector.cons a w) ω := by
  unfold firstPileEdges
  rw [anchoredEdges_mem_word]
  simp_rw [firstPile_wordInterval cuts ω a]

/-- The global sorted shuffle graph is exactly the union of the exposed pile
future graphs, with the deterministic zero-based pile offsets. -/
theorem shuffleEdges_firstPile {k n d : ℕ} (cuts : Cuts k n (d+1))
    (ω : Sample cuts) (e : Fin (n-1)) :
    e ∈ shuffleEdges ω ↔ ∃ a : Fin k, (e.val : ℤ) ∈ firstPileEdges a (emptyPrefix k d) ω := by
  rw [shuffleEdges_mem_word]
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨w.head,(firstPileEdges_mem_word cuts ω w.head _ _).mpr ⟨w.tail,?_,?_⟩⟩
    · simp [emptyPrefix]
    · simpa only [List.Vector.cons_head_tail] using hw
  · rintro ⟨a,ha⟩
    obtain ⟨w,_,hw⟩ := (firstPileEdges_mem_word cuts ω a _ _).mp ha
    exact ⟨List.Vector.cons a w,hw⟩

end RiffleUpperV2.Localization
