import RiffleUpperV2.Reservoir.InteriorMatrix
import RiffleUpperV2.Reservoir.BackwardHistory
import RiffleUpperV2.Localization.CollisionMass

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration
attribute [local instance 2000] wordDecEq

def cylinderRows {k n d : ℕ} {cuts : Cuts k n d} (x : Prefix k d) (ω : Sample cuts) : Finset (Fin n) :=
  Finset.univ.filter fun r => (rowWord ω r).toList.take x.1.val=x.2.toList

def tailColumns {k d : ℕ} (x : Prefix k d) : Finset (Fin d) :=
  Finset.univ.filter fun j => x.1.val≤j.val

theorem interior_prefix_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (R : Finset (Fin n)) (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber R (tailColumns x) ω₀ ω) (r : Fin n) :
    (rowWord ω r).toList.take x.1.val=(rowWord ω₀ r).toList.take x.1.val := by
  have he : RiffleShuffle.truncate (Nat.le_of_lt_succ x.1.isLt) (rowWord ω r)=
      RiffleShuffle.truncate (Nat.le_of_lt_succ x.1.isLt) (rowWord ω₀ r) := by
    apply List.Vector.ext
    intro j
    have ht (w : Word k d) : (RiffleShuffle.truncate (Nat.le_of_lt_succ x.1.isLt) w).get j=
        w.get ⟨j.val,by have := j.isLt; have := x.1.isLt; omega⟩ := by
      simp [RiffleShuffle.truncate,List.Vector.get,List.Vector.toList,List.get_eq_getElem,Fin.cast]
    rw [ht,ht,RiffleLowerV2.rowWord_get,RiffleLowerV2.rowWord_get]
    apply h
    left
    simp only [tailColumns,Finset.mem_filter,Finset.mem_univ,true_and,not_le]
    exact j.isLt
  exact congrArg List.Vector.toList he

theorem interior_outside_word {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (J : Finset (Fin d)) (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber R J ω₀ ω) (r : Fin n) (hr : r∉R) : rowWord ω r=rowWord ω₀ r := by
  apply List.Vector.ext
  intro j
  simpa only [RiffleLowerV2.rowWord_get] using h j r (Or.inr hr)

theorem interior_cylinderRows_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (R : Finset (Fin n)) (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber R (tailColumns x) ω₀ ω) : cylinderRows x ω=cylinderRows x ω₀ := by
  apply Finset.filter_congr
  intro r _
  rw [interior_prefix_eq cuts x R ω₀ ω h r]

/-- Every full word disjoint from the selected cylinder has exactly its
old multiplicity under arbitrary induced-count interior replacement. -/
theorem interior_wordCount_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d)
    (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber (cylinderRows x ω₀) (tailColumns x) ω₀ ω)
    (u : Word k d) (hu : ∀ w : Word k d, w.toList.take x.1.val=x.2.toList → w≠u) :
    wordCount ω u=wordCount ω₀ u := by
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r _
  by_cases hr : r∈cylinderRows x ω₀
  · have h0 : (rowWord ω₀ r).toList.take x.1.val=x.2.toList := (Finset.mem_filter.mp hr).2
    have h1 : (rowWord ω r).toList.take x.1.val=x.2.toList :=
      (interior_prefix_eq cuts x _ ω₀ ω h r).trans h0
    exact iff_of_false (hu _ h1) (hu _ h0)
  · rw [interior_outside_word cuts _ _ ω₀ ω h r hr]

/-- Interior replacements in a strict future cylinder preserve the literal
forward natural history and the full current multiplicity. -/
theorem interior_history_forward {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ωhist : Sample cuts) (j : Fin (pileSize cuts p))
    (x : Prefix k (L+1))
    (hfuture : ∀ w : Word k (L+1), w.toList.take x.1.val=x.2.toList → pileWords cuts p ωhist j<w)
    (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber (cylinderRows x ω₀) (tailColumns x) ω₀ ω)
    (h0 : historyFiber cuts p .forward (j.val+1) ωhist ω₀) :
    historyFiber cuts p .forward (j.val+1) ωhist ω ∧
      wordCount ω (pileWords cuts p ωhist j)=wordCount ω₀ (pileWords cuts p ωhist j) := by
  have hc (u : Word k (L+1)) (hu : u≤pileWords cuts p ωhist j) : wordCount ω u=wordCount ω₀ u :=
    interior_wordCount_eq cuts x ω₀ ω h u (fun w hw he => by
      have ht := hfuture w hw
      rw [he] at ht
      exact (not_lt_of_ge hu) ht)
  refine ⟨?_,hc _ le_rfl⟩
  rw [historyAtom] at h0 ⊢
  exact ⟨fun u hp hu => (hc u hu.le).trans (h0.1 u hp hu),by rw [hc _ le_rfl]; exact h0.2⟩

/-- Backward histories reverse spatial comparison only; the same interior
replacement keeps all column indices unchanged. -/
theorem interior_history_backward {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ωhist : Sample cuts) (j : Fin (pileSize cuts p))
    (x : Prefix k (L+1))
    (hfuture : ∀ w : Word k (L+1), w.toList.take x.1.val=x.2.toList → w<backwardWords cuts p ωhist j)
    (ω₀ ω : Sample cuts)
    (h : interiorMatrixFiber (cylinderRows x ω₀) (tailColumns x) ω₀ ω)
    (h0 : historyFiber cuts p .backward (j.val+1) ωhist ω₀) :
    historyFiber cuts p .backward (j.val+1) ωhist ω ∧
      wordCount ω (backwardWords cuts p ωhist j)=wordCount ω₀ (backwardWords cuts p ωhist j) := by
  have hc (u : Word k (L+1)) (hu : backwardWords cuts p ωhist j≤u) : wordCount ω u=wordCount ω₀ u :=
    interior_wordCount_eq cuts x ω₀ ω h u (fun w hw he => by
      have ht := hfuture w hw
      rw [he] at ht
      exact (not_lt_of_ge hu) ht)
  refine ⟨?_,hc _ le_rfl⟩
  rw [historyAtom_backward] at h0 ⊢
  exact ⟨fun u hp hu => (hc u hu.le).trans (h0.1 u hp hu),by rw [hc _ le_rfl]; exact h0.2⟩

end RiffleUpperV2.Reservoir
