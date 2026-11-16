import RiffleLowerV2.Model.FiniteLaws

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace RiffleLowerV2.Model
open TimeProfile

/-- A stable sort by the first key after a stable sort of the remaining keys. -/
theorem sort_cons {N : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin N → α) (g : Fin N → List α) :
    Tuple.sort (fun i => f i :: g i) =
      (Tuple.sort (fun i => f (Tuple.sort g i))).trans (Tuple.sort g) := by
  let s := Tuple.sort g
  let t := Tuple.sort (fun i => f (s i))
  change Tuple.sort (fun i => f i :: g i) = t.trans s
  symm
  apply Tuple.eq_sort_iff.mpr
  constructor
  · intro i j hij
    change f (s (t i)) :: g (s (t i)) ≤ f (s (t j)) :: g (s (t j))
    by_cases he : i = j
    · subst j
      exact le_rfl
    have ht := Tuple.monotone_sort (fun i => f (s i)) hij
    change f (s (t i)) ≤ f (s (t j)) at ht
    rcases ht.eq_or_lt with heq | hlt
    · have htij : t i < t j :=
        (Tuple.eq_sort_iff.mp (rfl : t = Tuple.sort (fun i => f (s i)))).2
          i j (lt_of_le_of_ne hij he) heq
      have hs := Tuple.monotone_sort g htij.le
      change g (s (t i)) ≤ g (s (t j)) at hs
      rw [heq]
      exact List.cons_le_cons _ hs
    · exact le_of_lt (List.Lex.rel hlt)
  · intro i j hij heq
    change f (s (t i)) :: g (s (t i)) = f (s (t j)) :: g (s (t j)) at heq
    have hh := List.cons.inj heq
    have htij : t i < t j :=
      (Tuple.eq_sort_iff.mp (rfl : t = Tuple.sort (fun i => f (s i)))).2 i j hij hh.1
    exact (Tuple.eq_sort_iff.mp (rfl : s = Tuple.sort g)).2 (t i) (t j) htij hh.2

/-- Selected columns in the given chronological order, viewed as a list key. -/
def physicalRowList {k N K : ℕ} {cuts : Cuts k N K}
    (l : List (Fin K)) (ω : Sample cuts) (i : Fin N) : List (Fin k) :=
  l.map (fun j => (ω j).val i)

def physicalListSort {k N K : ℕ} {cuts : Cuts k N K}
    (l : List (Fin K)) (ω : Sample cuts) : Permutation N :=
  Tuple.sort (physicalRowList l ω)

/-- The inverse of the chronological forward composition on a list of times. -/
def physicalInverseList {k N K : ℕ} {cuts : Cuts k N K}
    (l : List (Fin K)) (ω : Sample cuts) : Permutation N :=
  l.foldr (fun j deck => (Tuple.sort (ω j).val).trans deck) (Equiv.refl _)

theorem physicalInverseList_foldl {k N K : ℕ} {cuts : Cuts k N K}
    (l : List (Fin K)) (ω : Sample cuts) (deck : Permutation N) :
    (l.foldl (fun deck j => ((Tuple.sort (ω j).val).symm).trans deck) deck).symm =
      deck.symm.trans (physicalInverseList l ω) := by
  induction l generalizing deck with
  | nil => simp [physicalInverseList]
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    simp [physicalInverseList, Equiv.symm_trans, Equiv.trans_assoc]

theorem physicalInverseList_full {k N K : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) : physicalInverseList (List.finRange K) ω = physicalInverse ω := by
  simpa [physicalInverse, physicalForward, oneStepForward] using
    (physicalInverseList_foldl (List.finRange K) ω (Equiv.refl _)).symm

theorem physicalRowList_update {k N K : ℕ} {cuts : Cuts k N K}
    (l : List (Fin K)) (j : Fin K) (hj : j ∉ l) (ω : Sample cuts)
    (a : ColumnAssignments cuts j) :
    physicalRowList l (Function.update ω j a) = physicalRowList l ω := by
  funext i
  apply List.map_congr_left
  intro t ht
  have htj : t ≠ j := fun h => hj (h ▸ ht)
  simp [Function.update_of_ne htj]

theorem physicalListSort_update {k N K : ℕ} {cuts : Cuts k N K}
    (l : List (Fin K)) (j : Fin K) (hj : j ∉ l) (ω : Sample cuts)
    (a : ColumnAssignments cuts j) :
    physicalListSort l (Function.update ω j a) = physicalListSort l ω := by
  unfold physicalListSort
  rw [physicalRowList_update l j hj]

/-- A coordinate pullback whose sorting permutation uses only the other coordinates. -/
def physicalColumnShear {k N K : ℕ} (cuts : Cuts k N K)
    (j : Fin K) (l : List (Fin K)) (hj : j ∉ l) : Sample cuts ≃ Sample cuts where
  toFun ω := Function.update ω j
    (columnEquiv cuts j (physicalListSort l ω).symm (ω j))
  invFun ω := Function.update ω j
    (columnEquiv cuts j (physicalListSort l ω) (ω j))
  left_inv ω := by
    dsimp only
    rw [physicalListSort_update l j hj]
    funext t
    by_cases ht : t = j
    · subst t
      simp only [Function.update_self]
      apply Subtype.ext
      funext i
      simp
    · simp [Function.update_of_ne ht]
  right_inv ω := by
    dsimp only
    rw [physicalListSort_update l j hj]
    funext t
    by_cases ht : t = j
    · subst t
      simp only [Function.update_self]
      apply Subtype.ext
      funext i
      simp
    · simp [Function.update_of_ne ht]

theorem physicalColumnShear_other {k N K : ℕ} (cuts : Cuts k N K)
    (j : Fin K) (l : List (Fin K)) (hj : j ∉ l) (ω : Sample cuts)
    (t : Fin K) (ht : t ≠ j) : physicalColumnShear cuts j l hj ω t = ω t := by
  exact Function.update_of_ne ht _ _

/-- Reverse-time pullback of current-position digit assignments to original labels. -/
def physicalPullback {k N K : ℕ} (cuts : Cuts k N K) :
    (l : List (Fin K)) → l.Nodup → Sample cuts ≃ Sample cuts
  | [], _ => Equiv.refl _
  | j :: l, h => (physicalPullback cuts l h.of_cons).trans
      (physicalColumnShear cuts j l (List.nodup_cons.mp h).1)

theorem physicalPullback_other {k N K : ℕ} (cuts : Cuts k N K)
    (l : List (Fin K)) (h : l.Nodup) (ω : Sample cuts)
    (j : Fin K) (hj : j ∉ l) : physicalPullback cuts l h ω j = ω j := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    have hjt : j ≠ t := fun he => hj (by simp [he])
    have hjl : j ∉ l := fun he => hj (List.mem_cons_of_mem _ he)
    change physicalColumnShear cuts t l (List.nodup_cons.mp h).1
      (physicalPullback cuts l h.of_cons ω) j = ω j
    rw [physicalColumnShear_other _ _ _ _ _ _ hjt]
    exact ih h.of_cons hjl

theorem physicalListSort_shear {k N K : ℕ} (cuts : Cuts k N K)
    (j : Fin K) (l : List (Fin K)) (hj : j ∉ l) (ω : Sample cuts) :
    physicalListSort (j :: l) (physicalColumnShear cuts j l hj ω) =
      (Tuple.sort (ω j).val).trans (physicalListSort l ω) := by
  have hrow : physicalRowList (j :: l) (physicalColumnShear cuts j l hj ω) =
      fun i => (ω j).val ((physicalListSort l ω).symm i) :: physicalRowList l ω i := by
    funext i
    change _ :: physicalRowList l (physicalColumnShear cuts j l hj ω) i = _
    rw [show physicalRowList l (physicalColumnShear cuts j l hj ω) =
      physicalRowList l ω from physicalRowList_update l j hj ω _]
    change (Function.update ω j
      (columnEquiv cuts j (physicalListSort l ω).symm (ω j)) j).val i ::
        physicalRowList l ω i = _
    simp
  unfold physicalListSort
  rw [hrow, sort_cons]
  simp only [physicalListSort, Equiv.symm_apply_apply]

theorem physicalPullback_sort {k N K : ℕ} (cuts : Cuts k N K)
    (l : List (Fin K)) (h : l.Nodup) (ω : Sample cuts) :
    physicalListSort l (physicalPullback cuts l h ω) = physicalInverseList l ω := by
  induction l with
  | nil =>
    apply Tuple.sort_eq_refl_iff_monotone.mpr
    intro i j hij
    exact le_rfl
  | cons j l ih =>
    change physicalListSort (j :: l)
      (physicalColumnShear cuts j l (List.nodup_cons.mp h).1
        (physicalPullback cuts l h.of_cons ω)) = _
    rw [physicalListSort_shear, physicalPullback_other cuts l h.of_cons ω j
      (List.nodup_cons.mp h).1,
      ih h.of_cons]
    rfl

theorem physicalRowList_full {k N K : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) (i : Fin N) :
    physicalRowList (List.finRange K) ω i = (rowWord ω i).toList := by
  simp [physicalRowList, rowWord, List.Vector.toList_ofFn, List.ofFn_eq_map,
    sampleRow, sampleEntry]

theorem physicalListSort_full {k N K : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) : physicalListSort (List.finRange K) ω = stableSort ω := by
  apply Tuple.eq_sort_iff.mpr
  constructor
  · intro i j hij
    change (rowWord ω (physicalListSort (List.finRange K) ω i)).toList ≤
      (rowWord ω (physicalListSort (List.finRange K) ω j)).toList
    simp only [← physicalRowList_full]
    exact Tuple.monotone_sort (physicalRowList (List.finRange K) ω) hij
  · intro i j hij heq
    have heq' := congrArg (fun w : Word k K => w.toList) heq
    simp only [← physicalRowList_full] at heq'
    exact (Tuple.eq_sort_iff.mp
      (rfl : physicalListSort (List.finRange K) ω =
        Tuple.sort (physicalRowList (List.finRange K) ω))).2 i j hij heq'

/-- The actual triangular bijection of canonical fixed-count samples. -/
def physicalPullbackEquiv {k N K : ℕ} (cuts : Cuts k N K) : Sample cuts ≃ Sample cuts :=
  physicalPullback cuts (List.finRange K) (List.nodup_finRange K)

theorem stableSort_physicalPullback {k N K : ℕ} (cuts : Cuts k N K) (ω : Sample cuts) :
    stableSort (physicalPullbackEquiv cuts ω) = physicalInverse ω := by
  rw [← physicalListSort_full]
  exact (physicalPullback_sort cuts (List.finRange K) (List.nodup_finRange K) ω).trans
    (physicalInverseList_full ω)

theorem physicalMatrixBridge : Targets.PhysicalMatrixBridge := by
  intro k N K cuts
  have hu : (fixedCountPMF cuts).map (physicalPullbackEquiv cuts) = fixedCountPMF cuts :=
    map_uniform_equiv (physicalPullbackEquiv cuts)
  have hm := congrArg (fun P : PMF (Sample cuts) => P.map stableSort) hu
  rw [PMF.map_comp] at hm
  simpa only [Function.comp_def, stableSort_physicalPullback,
    physicalInverseLaw, matrixLaw] using hm

end RiffleLowerV2.Model
