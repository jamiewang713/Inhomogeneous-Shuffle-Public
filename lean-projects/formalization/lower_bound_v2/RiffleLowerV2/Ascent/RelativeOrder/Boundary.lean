import RiffleLowerV2.Ascent.RelativeOrder.Weighted

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Ascent

variable {N : ℕ}

def Separates (A B : Finset (Fin N)) (π : Permutation N) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, π x < π y

theorem exists_separates (A B : Finset (Fin N)) (hAB : Disjoint A B) :
    ∃ τ : Permutation N, Separates A B τ := by
  let key : Fin N → ℕ := fun x => if x ∈ A then 0 else 1
  let p := Tuple.sort key
  refine ⟨p.symm, ?_⟩
  intro x hx y hy
  have hyA : y ∉ A := fun ha => Finset.disjoint_left.mp hAB ha hy
  by_contra hn
  have hle : p.symm y ≤ p.symm x := le_of_not_gt hn
  have hm := Tuple.monotone_sort key hle
  simp [p, key, hx, hyA] at hm

theorem union_relativeOrder_iff (A B : Finset (Fin N))
    (π τ : Permutation N) (hτ : Separates A B τ) :
    relativeOrder (A ∪ B) π = relativeOrder (A ∪ B) τ ↔
      Separates A B π ∧ relativeOrder A π = relativeOrder A τ ∧
        relativeOrder B π = relativeOrder B τ := by
  simp only [relativeOrder_eq_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy
      exact (h x (Finset.mem_union_left B hx) y (Finset.mem_union_right A hy)).mpr
        (hτ x hx y hy)
    · intro x hx y hy
      exact h x (Finset.mem_union_left B hx) y (Finset.mem_union_left B hy)
    · intro x hx y hy
      exact h x (Finset.mem_union_right A hx) y (Finset.mem_union_right A hy)
  · rintro ⟨hπ, hA, hB⟩ x hx y hy
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact hA x hx y hy
    · exact iff_of_true (hπ x hx y hy) (hτ x hx y hy)
    · exact iff_of_false (not_lt_of_gt (hπ y hy x hx)) (not_lt_of_gt (hτ y hy x hx))
    · exact hB x hx y hy

def pairSets (A B : Finset (Fin N)) : Bool → Finset (Fin N) :=
  fun b => if b then B else A

theorem pairSets_disjoint (A B : Finset (Fin N)) (hAB : Disjoint A B) :
    ∀ i j : Bool, i ≠ j → Disjoint (pairSets A B i) (pairSets A B j) := by
  intro i j hij
  cases i <;> cases j <;> simp_all [pairSets, disjoint_comm]

theorem separates_blockAction (A B : Finset (Fin N)) (hAB : Disjoint A B)
    (η : ∀ i, Equiv.Perm (Fin (pairSets A B i).card)) (π : Permutation N) :
    Separates A B ((blockAction (pairSets A B) (pairSets_disjoint A B hAB) η).trans π) ↔
      Separates A B π := by
  let p := blockAction (pairSets A B) (pairSets_disjoint A B hAB) η
  have hmA {x : Fin N} (hx : x ∈ A) : p x ∈ A :=
    blockAction_mem (pairSets A B) (pairSets_disjoint A B hAB) η false hx
  have hmB {x : Fin N} (hx : x ∈ B) : p x ∈ B :=
    blockAction_mem (pairSets A B) (pairSets_disjoint A B hAB) η true hx
  have hiA {x : Fin N} (hx : x ∈ A) : p.symm x ∈ A :=
    blockAction_symm_mem (pairSets A B) (pairSets_disjoint A B hAB) η false hx
  have hiB {x : Fin N} (hx : x ∈ B) : p.symm x ∈ B :=
    blockAction_symm_mem (pairSets A B) (pairSets_disjoint A B hAB) η true hx
  constructor
  · intro h x hx y hy
    have hh := h (p.symm x) (hiA hx) (p.symm y) (hiB hy)
    simpa only [Equiv.trans_apply, ← show blockAction (pairSets A B)
      (pairSets_disjoint A B hAB) η = p from rfl, Equiv.apply_symm_apply] using hh
  · intro h x hx y hy
    exact h (p x) (hmA hx) (p y) (hmB hy)

theorem boundaryAscentProbability : Targets.BoundaryAscentProbability := by
  intro N A B hAB
  obtain ⟨τ, hτ⟩ := exists_separates A B hAB
  have h := probability_and_relativeOrder (pairSets A B) (pairSets_disjoint A B hAB)
    (Separates A B) (separates_blockAction A B hAB) τ
  have hevent : (fun π : Permutation N => Separates A B π ∧
      ∀ i, relativeOrder (pairSets A B i) π = relativeOrder (pairSets A B i) τ) =
      (fun π => ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, (π x < π y ↔ τ x < τ y)) := by
    funext π
    apply propext
    simpa [pairSets, Bool.forall_bool, and_assoc] using
      (union_relativeOrder_iff A B π τ hτ).symm.trans (relativeOrder_eq_iff _ _ _)
  rw [hevent, probability_relativeOrder] at h
  simp only [Fintype.prod_bool, pairSets, Bool.false_eq_true, if_false, if_true] at h
  have hcard : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB
  rw [hcard] at h
  have hfA : (A.card.factorial : ℝ) ≠ 0 := by positivity
  have hfB : (B.card.factorial : ℝ) ≠ 0 := by positivity
  have hc := congrArg (fun n : ℕ => (n : ℝ))
    (Nat.add_choose_mul_factorial_mul_factorial A.card B.card)
  rw [← Nat.choose_symm_add] at hc
  simp only [Nat.cast_mul] at hc
  have hcpos : (0 : ℝ) < ((A.card+B.card).choose A.card : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right A.card B.card)
  change probability (uniformPermutation N) (Separates A B) = _
  field_simp [hfA, hfB] at h
  apply (eq_div_iff hcpos.ne').mpr
  apply (mul_right_cancel₀ (mul_ne_zero hfA hfB))
  calc
    _ = probability (uniformPermutation N) (Separates A B) *
        ((A.card+B.card).choose A.card * A.card.factorial * B.card.factorial : ℝ) := by ring
    _ = probability (uniformPermutation N) (Separates A B) *
        ((A.card+B.card).factorial : ℝ) := by rw [hc]
    _ = _ := by nlinarith [h]

end RiffleLowerV2.Ascent
