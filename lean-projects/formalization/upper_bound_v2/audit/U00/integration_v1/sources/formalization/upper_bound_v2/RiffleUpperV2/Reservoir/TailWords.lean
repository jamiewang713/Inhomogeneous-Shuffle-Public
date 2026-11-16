import RiffleUpperV2.Reservoir.InducedMatrix

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

def wordSuffix {k d : ℕ} (x : Prefix k d) (w : Word k d) : Word k (d-x.1.val) :=
  ⟨w.toList.drop x.1.val,by simp⟩

theorem wordSuffix_get {k d : ℕ} (x : Prefix k d) (w : Word k d) (j : Fin (d-x.1.val)) :
    (wordSuffix x w).get j=w.get (suffixColumn x j) := by
  simp [wordSuffix,suffixColumn,List.Vector.get,List.Vector.toList,List.get_eq_getElem]

theorem word_prefix_suffix {k d : ℕ} (x : Prefix k d) (w : Word k d)
    (hw : w.toList.take x.1.val=x.2.toList) : w.toList=x.2.toList++(wordSuffix x w).toList := by
  rw [← hw]
  exact (List.take_append_drop x.1.val w.toList).symm

theorem list_append_lt_cancel {k : ℕ} (a b c : List (Fin k)) : (a++b<a++c ↔ b<c) := by
  induction a with
  | nil => rfl
  | cons z a ih =>
    change List.Lex (· < ·) (z :: (a++b)) (z :: (a++c)) ↔ b<c
    rw [List.lex_cons_iff]
    exact ih

theorem wordSuffix_compare {k d : ℕ} (x : Prefix k d) (w z : Word k d)
    (hw : w.toList.take x.1.val=x.2.toList) (hz : z.toList.take x.1.val=x.2.toList) :
    (w≤z ↔ wordSuffix x w≤wordSuffix x z) ∧ (w=z ↔ wordSuffix x w=wordSuffix x z) := by
  have he : w=z ↔ wordSuffix x w=wordSuffix x z := by
    constructor
    · exact congrArg _
    · intro hh
      apply List.Vector.toList_injective
      rw [word_prefix_suffix x w hw,word_prefix_suffix x z hz,hh]
  have ht : w<z ↔ wordSuffix x w<wordSuffix x z := by
    change w.toList<z.toList ↔ _
    rw [word_prefix_suffix x w hw,word_prefix_suffix x z hz,list_append_lt_cancel]
    rfl
  exact ⟨by simpa only [le_iff_eq_or_lt,he,ht],he⟩

/-- Sorting depends only on pairwise word comparison, including the original
label tie breaker. Thus deleting a common prefix preserves the sort. -/
theorem sort_eq_of_comparison {n : ℕ} {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : Fin n → α) (g : Fin n → β)
    (hle : ∀ i j, f i≤f j ↔ g i≤g j) (heq : ∀ i j, f i=f j ↔ g i=g j) :
    Tuple.sort f=Tuple.sort g := by
  symm
  apply Tuple.eq_sort_iff.mpr
  have hg := (Tuple.eq_sort_iff (f := g) (σ := Tuple.sort g)).mp rfl
  constructor
  · intro i j hij
    exact (hle _ _).mpr (hg.1 hij)
  · intro i j hij hf
    exact hg.2 i j hij ((heq _ _).mp hf)

def blockWords {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n)) (ω : Sample cuts) : Fin R.card → Word k d :=
  fun i => rowWord ω (R.equivFin.symm i).val

def blockGraph {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n)) (ω : Sample cuts) : PathEdges R.card :=
  RiffleLowerV2.Model.keyEdges (blockWords R ω ∘ Tuple.sort (blockWords R ω))

theorem inducedMatrix_rowWord {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n)) (x : Prefix k d)
    (ω₀ ω : Sample cuts) (hc : interiorCountsEq R (tailColumns x) ω₀ ω) (i : Fin R.card) :
    rowWord (inducedMatrixEquiv cuts R x ω₀ (projectInterior R (tailColumns x) ω₀ ω hc)) i=
      wordSuffix x (blockWords R ω i) := by
  apply List.Vector.ext
  intro j
  rw [RiffleLowerV2.rowWord_get,wordSuffix_get]
  change sampleEntry (inducedMatrixEquiv cuts R x ω₀ (projectInterior R (tailColumns x) ω₀ ω hc)) i j=
    (rowWord ω (R.equivFin.symm i).val).get (suffixColumn x j)
  rw [RiffleLowerV2.rowWord_get]
  rfl

/-- The actual sorted full-word graph on a labeled cylinder is the existing
shuffle graph of its induced tail matrix, without changing column order. -/
theorem blockGraph_eq_induced {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n)) (x : Prefix k d)
    (ω₀ ω : Sample cuts) (hc : interiorCountsEq R (tailColumns x) ω₀ ω)
    (hprefix : ∀ r∈R, (rowWord ω r).toList.take x.1.val=x.2.toList) :
    blockGraph R ω=shuffleEdges (inducedMatrixEquiv cuts R x ω₀ (projectInterior R (tailColumns x) ω₀ ω hc)) := by
  let σ := inducedMatrixEquiv cuts R x ω₀ (projectInterior R (tailColumns x) ω₀ ω hc)
  have hp (i : Fin R.card) := hprefix (R.equivFin.symm i).val (R.equivFin.symm i).property
  have heq (i j : Fin R.card) : blockWords R ω i=blockWords R ω j ↔ rowWord σ i=rowWord σ j := by
    rw [inducedMatrix_rowWord,inducedMatrix_rowWord]
    exact (wordSuffix_compare x _ _ (hp i) (hp j)).2
  have hle (i j : Fin R.card) : blockWords R ω i≤blockWords R ω j ↔ rowWord σ i≤rowWord σ j := by
    rw [inducedMatrix_rowWord,inducedMatrix_rowWord]
    exact (wordSuffix_compare x _ _ (hp i) (hp j)).1
  have hs := sort_eq_of_comparison (blockWords R ω) (rowWord σ) hle heq
  unfold blockGraph
  rw [hs]
  change RiffleLowerV2.Model.keyEdges (blockWords R ω ∘ Tuple.sort (rowWord σ))=RiffleLowerV2.shuffleEdges σ
  rw [← RiffleLowerV2.Model.keyEdges_sortedWord]
  ext e
  simp only [RiffleLowerV2.Model.mem_keyEdges,Function.comp_apply]
  exact heq _ _

end RiffleUpperV2.Reservoir
