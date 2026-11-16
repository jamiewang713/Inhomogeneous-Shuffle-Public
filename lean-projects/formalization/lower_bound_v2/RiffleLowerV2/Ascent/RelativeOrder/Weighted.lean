import RiffleLowerV2.Ascent.RelativeOrder.Law

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Ascent

variable {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- Relative orders are also independent of every observable invariant under block reordering. -/
theorem relativeOrder_weighted_expect (A : I → Finset (Fin N))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (w : Permutation N → ℝ)
    (hw : ∀ η π, w ((blockAction A hA η).trans π) = w π)
    (F : (∀ i, Equiv.Perm (Fin (A i).card)) → ℝ) :
    expect (uniformPermutation N) (fun π => w π * F (fun i => relativeOrder (A i) π)) =
      expect (uniformPermutation N) w *
        expect (PMF.uniformOfFintype (∀ i, Equiv.Perm (Fin (A i).card))) F := by
  let Q := ∀ i, Equiv.Perm (Fin (A i).card)
  let f : Permutation N → ℝ := fun π => w π * F (fun i => relativeOrder (A i) π)
  have hcol (η : Q) :
      (∑ π : Permutation N, f ((blockAction A hA η).trans π)) = ∑ π, f π :=
    (leftPositionAction (blockAction A hA η)).sum_comp f
  have hrow (π : Permutation N) :
      (∑ η : Q, f ((blockAction A hA η).trans π)) = w π * ∑ η : Q, F η := by
    simp only [f, hw, ← Finset.mul_sum]
    congr 1
    let e : Q ≃ Q := Equiv.piCongrRight fun i => orderTransform (relativeOrder (A i) π)
    convert e.sum_comp F using 1
    apply Finset.sum_congr rfl
    intro η _
    apply congrArg F
    funext i
    exact relativeOrder_blockAction A hA η π i
  have hcount : (Fintype.card Q : ℝ) * (∑ π : Permutation N, f π) =
      (∑ π : Permutation N, w π) * (∑ η : Q, F η) := by
    calc
      _ = ∑ η : Q, ∑ π : Permutation N, f ((blockAction A hA η).trans π) := by
        simp only [hcol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ π : Permutation N, ∑ η : Q, f ((blockAction A hA η).trans π) :=
        Finset.sum_comm
      _ = _ := by simp only [hrow, Finset.sum_mul]
  rw [uniformPermutation, expect_uniform, expect_uniform, expect_uniform]
  change (∑ π : Permutation N, f π) / Fintype.card (Permutation N) =
    ((∑ π : Permutation N, w π) / Fintype.card (Permutation N)) *
      ((∑ η : Q, F η) / Fintype.card Q)
  have hQ : (Fintype.card Q : ℝ) ≠ 0 := by positivity
  have hP : (Fintype.card (Permutation N) : ℝ) ≠ 0 := by positivity
  field_simp [hQ, hP]
  nlinarith [hcount]

theorem probability_relativeOrder (A : Finset (Fin N)) (τ : Permutation N) :
    probability (uniformPermutation N)
      (fun π => ∀ x ∈ A, ∀ y ∈ A, (π x < π y ↔ τ x < τ y)) =
      1 / (A.card.factorial : ℝ) := by
  have h := relativeOrder_expect_single A
    (fun ρ => if ρ = relativeOrder A τ then (1 : ℝ) else 0)
  rw [expect_uniform] at h
  have hevent : (fun π : Permutation N => if relativeOrder A π = relativeOrder A τ
      then (1 : ℝ) else 0) =
      (fun π => if ∀ x ∈ A, ∀ y ∈ A, (π x < π y ↔ τ x < τ y)
        then (1 : ℝ) else 0) := by
    funext π
    simp only [relativeOrder_eq_iff]
  rw [hevent] at h
  convert h using 1
  · unfold probability
    congr 1
    funext π
    split_ifs <;> rfl
  · simp [Fintype.card_perm]

theorem probability_and_relativeOrder (A : I → Finset (Fin N))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (S : Permutation N → Prop)
    (hS : ∀ η π, S ((blockAction A hA η).trans π) ↔ S π)
    (τ : Permutation N) :
    probability (uniformPermutation N)
      (fun π => S π ∧ ∀ i, relativeOrder (A i) π = relativeOrder (A i) τ) =
      probability (uniformPermutation N) S * ∏ i, 1 / ((A i).card.factorial : ℝ) := by
  let w : Permutation N → ℝ := fun π => if S π then 1 else 0
  have hw : ∀ η π, w ((blockAction A hA η).trans π) = w π := by
    intro η π
    simp only [w, hS]
  have h := relativeOrder_weighted_expect A hA w hw
    (fun η => if η = (fun i => relativeOrder (A i) τ) then (1 : ℝ) else 0)
  have heq (π : Permutation N) :
      w π * (if (fun i => relativeOrder (A i) π) = (fun i => relativeOrder (A i) τ)
        then (1 : ℝ) else 0) =
      if S π ∧ ∀ i, relativeOrder (A i) π = relativeOrder (A i) τ then (1 : ℝ) else 0 := by
    simp only [w, funext_iff]
    by_cases hs : S π <;>
      by_cases hr : ∀ i, relativeOrder (A i) π = relativeOrder (A i) τ <;> simp [hs, hr]
  simp only [heq] at h
  rw [expect_indicator] at h
  have hw' : expect (uniformPermutation N) w = probability (uniformPermutation N) S :=
    expect_indicator _ _
  rw [hw', expect_uniform] at h
  simpa [Fintype.card_pi, Fintype.card_perm, Nat.cast_prod,
    Finset.prod_inv_distrib, one_div] using h

end RiffleLowerV2.Ascent
