import Contracts.v1.AdditionalFinite

/-! Exact order coordinates and the simultaneous action on disjoint position sets. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Ascent

variable {N : ℕ}

def positionEnum (A : Finset (Fin N)) : Fin A.card ≃ A :=
  (A.orderIsoOfFin rfl).toEquiv

def relativeOrder (A : Finset (Fin N)) (π : Permutation N) : Equiv.Perm (Fin A.card) :=
  Tuple.sort (fun i => π (positionEnum A i))

theorem relativeOrder_strictMono (A : Finset (Fin N)) (π : Permutation N) :
    StrictMono (fun i => π (positionEnum A (relativeOrder A π i))) := by
  apply (Tuple.monotone_sort (fun i : Fin A.card => π (positionEnum A i))).strictMono_of_injective
  exact π.injective.comp (Subtype.val_injective.comp
    ((positionEnum A).injective.comp (relativeOrder A π).injective))

theorem relativeOrder_lt_iff (A : Finset (Fin N)) (π : Permutation N)
    (x y : Fin A.card) :
    π (positionEnum A x) < π (positionEnum A y) ↔
      (relativeOrder A π).symm x < (relativeOrder A π).symm y := by
  have h := (relativeOrder_strictMono A π).lt_iff_lt
    (a := (relativeOrder A π).symm x) (b := (relativeOrder A π).symm y)
  simpa only [Equiv.apply_symm_apply] using h

theorem relativeOrder_eq_iff (A : Finset (Fin N)) (π σ : Permutation N) :
    relativeOrder A π = relativeOrder A σ ↔
      ∀ x ∈ A, ∀ y ∈ A, (π x < π y ↔ σ x < σ y) := by
  constructor
  · intro h x hx y hy
    let a := (positionEnum A).symm ⟨x, hx⟩
    let b := (positionEnum A).symm ⟨y, hy⟩
    have hπ := relativeOrder_lt_iff A π a b
    have hσ := relativeOrder_lt_iff A σ a b
    rw [h] at hπ
    simpa [a, b] using hπ.trans hσ.symm
  · intro h
    have hmono : StrictMono (fun i => σ (positionEnum A (relativeOrder A π i))) := by
      intro i j hij
      apply (h _ (positionEnum A _).property _ (positionEnum A _).property).mp
      exact relativeOrder_strictMono A π hij
    have heq := Tuple.unique_monotone (f := fun i : Fin A.card => σ (positionEnum A i))
      (σ := relativeOrder A π) (τ := relativeOrder A σ) hmono.monotone
      (relativeOrder_strictMono A σ).monotone
    apply Equiv.ext
    intro i
    exact (positionEnum A).injective (Subtype.ext
      (σ.injective (congrFun heq i)))

section DisjointAction

variable {I : Type*} [Fintype I]
variable (A : I → Finset (Fin N))
variable (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))

def blockMap (η : ∀ i, Equiv.Perm (Fin (A i).card)) (x : Fin N) : Fin N :=
  if hx : ∃ i, x ∈ A i then
    let i := Classical.choose hx
    positionEnum (A i) (η i ((positionEnum (A i)).symm ⟨x, Classical.choose_spec hx⟩))
  else x

include hA

theorem blockMap_apply (η : ∀ i, Equiv.Perm (Fin (A i).card))
    (i : I) (x : Fin (A i).card) :
    blockMap A η (positionEnum (A i) x) = positionEnum (A i) (η i x) := by
  have hx : ∃ j, (positionEnum (A i) x : Fin N) ∈ A j :=
    ⟨i, (positionEnum (A i) x).property⟩
  have hi : Classical.choose hx = i := by
    by_contra hn
    exact Finset.disjoint_left.mp (hA _ _ hn) (Classical.choose_spec hx)
      (positionEnum (A i) x).property
  simp only [blockMap, dif_pos hx]
  have heq (j : I) (hj : (positionEnum (A i) x : Fin N) ∈ A j) (hji : j = i) :
      (positionEnum (A j) (η j ((positionEnum (A j)).symm
        ⟨(positionEnum (A i) x : Fin N), hj⟩)) : Fin N) =
        positionEnum (A i) (η i x) := by
    subst j
    simp
  exact heq _ _ hi

theorem blockMap_apply_of_mem (η : ∀ i, Equiv.Perm (Fin (A i).card))
    (i : I) (x : Fin N) (hx : x ∈ A i) :
    blockMap A η x =
      positionEnum (A i) (η i ((positionEnum (A i)).symm ⟨x, hx⟩)) := by
  convert blockMap_apply A hA η i ((positionEnum (A i)).symm ⟨x, hx⟩) using 1
  simp

def blockAction (η : ∀ i, Equiv.Perm (Fin (A i).card)) : Permutation N where
  toFun := blockMap A η
  invFun := blockMap A (fun i => (η i).symm)
  left_inv x := by
    by_cases hx : ∃ i, x ∈ A i
    · obtain ⟨i, hi⟩ := hx
      rw [blockMap_apply_of_mem A hA η i x hi, blockMap_apply A hA]
      simp
    · simp [blockMap, hx]
  right_inv x := by
    by_cases hx : ∃ i, x ∈ A i
    · obtain ⟨i, hi⟩ := hx
      rw [blockMap_apply_of_mem A hA (fun i => (η i).symm) i x hi,
        blockMap_apply A hA]
      simp
    · simp [blockMap, hx]

theorem blockAction_apply (η : ∀ i, Equiv.Perm (Fin (A i).card))
    (i : I) (x : Fin (A i).card) :
    blockAction A hA η (positionEnum (A i) x) = positionEnum (A i) (η i x) :=
  blockMap_apply A hA η i x

theorem blockAction_mem (η : ∀ i, Equiv.Perm (Fin (A i).card))
    (i : I) {x : Fin N} (hx : x ∈ A i) : blockAction A hA η x ∈ A i := by
  change blockMap A η x ∈ A i
  rw [blockMap_apply_of_mem A hA η i x hx]
  exact (positionEnum (A i) _).property

theorem blockAction_symm_mem (η : ∀ i, Equiv.Perm (Fin (A i).card))
    (i : I) {x : Fin N} (hx : x ∈ A i) : (blockAction A hA η).symm x ∈ A i := by
  change blockMap A (fun j => (η j).symm) x ∈ A i
  rw [blockMap_apply_of_mem A hA _ i x hx]
  exact (positionEnum (A i) _).property

theorem relativeOrder_blockAction (η : ∀ i, Equiv.Perm (Fin (A i).card))
    (π : Permutation N) (i : I) :
    relativeOrder (A i) ((blockAction A hA η).trans π) =
      (relativeOrder (A i) π).trans (η i).symm := by
  have hm : StrictMono (fun x => ((blockAction A hA η).trans π)
      (positionEnum (A i) (((relativeOrder (A i) π).trans (η i).symm) x))) := by
    simpa only [Equiv.trans_apply, blockAction_apply, Equiv.apply_symm_apply] using
      relativeOrder_strictMono (A i) π
  have heq := Tuple.unique_monotone
    (f := fun x : Fin (A i).card => ((blockAction A hA η).trans π) (positionEnum (A i) x))
    (σ := relativeOrder (A i) ((blockAction A hA η).trans π))
    (τ := (relativeOrder (A i) π).trans (η i).symm)
    (relativeOrder_strictMono (A i) ((blockAction A hA η).trans π)).monotone hm.monotone
  apply Equiv.ext
  intro x
  exact (positionEnum (A i)).injective (Subtype.ext
    (((blockAction A hA η).trans π).injective (congrFun heq x)))

end DisjointAction
end RiffleLowerV2.Ascent
