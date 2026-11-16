import RiffleLowerV2.Ascent.RelativeOrder.Basic
import RiffleLowerV2.Ascent.FiniteProbability

/-! Uniform joint relative-order law proved by a finite bijective averaging argument. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Ascent

variable {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

def orderTransform {n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun η := ρ.trans η.symm
  invFun η := η.symm.trans ρ
  left_inv η := by ext x; simp
  right_inv η := by ext x; simp

def leftPositionAction (ρ : Permutation N) : Permutation N ≃ Permutation N where
  toFun π := ρ.trans π
  invFun π := ρ.symm.trans π
  left_inv π := by ext x; simp
  right_inv π := by ext x; simp

/-- The entire vector of relative orders has the finite uniform product law. -/
theorem relativeOrder_expect (A : I → Finset (Fin N))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (F : (∀ i, Equiv.Perm (Fin (A i).card)) → ℝ) :
    expect (uniformPermutation N) (fun π => F (fun i => relativeOrder (A i) π)) =
      expect (PMF.uniformOfFintype (∀ i, Equiv.Perm (Fin (A i).card))) F := by
  let Q := ∀ i, Equiv.Perm (Fin (A i).card)
  let f : Permutation N → ℝ := fun π => F (fun i => relativeOrder (A i) π)
  have hcol (η : Q) :
      (∑ π : Permutation N, f ((blockAction A hA η).trans π)) = ∑ π, f π :=
    (leftPositionAction (blockAction A hA η)).sum_comp f
  have hrow (π : Permutation N) :
      (∑ η : Q, f ((blockAction A hA η).trans π)) = ∑ η : Q, F η := by
    let e : Q ≃ Q := Equiv.piCongrRight fun i => orderTransform (relativeOrder (A i) π)
    convert e.sum_comp F using 1
    apply Finset.sum_congr rfl
    intro η _
    apply congrArg F
    funext i
    exact relativeOrder_blockAction A hA η π i
  have hcount : (Fintype.card Q : ℝ) * (∑ π : Permutation N, f π) =
      (Fintype.card (Permutation N) : ℝ) * (∑ η : Q, F η) := by
    calc
      _ = ∑ η : Q, ∑ π : Permutation N, f ((blockAction A hA η).trans π) := by
        simp only [hcol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ π : Permutation N, ∑ η : Q, f ((blockAction A hA η).trans π) :=
        Finset.sum_comm
      _ = _ := by simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [uniformPermutation, expect_uniform, expect_uniform]
  change (∑ π : Permutation N, f π) / Fintype.card (Permutation N) =
    (∑ η : Q, F η) / Fintype.card Q
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  nlinarith [hcount]

/-- Marginal uniformity, including an empty selected set. -/
theorem relativeOrder_expect_single (A : Finset (Fin N))
    (f : Equiv.Perm (Fin A.card) → ℝ) :
    expect (uniformPermutation N) (fun π => f (relativeOrder A π)) =
      expect (PMF.uniformOfFintype (Equiv.Perm (Fin A.card))) f := by
  have h := relativeOrder_expect (I := Unit) (fun _ => A)
    (by intro i j hij; exact False.elim (hij (Subsingleton.elim i j)))
    (fun η => f (η ()))
  let e : (Unit → Equiv.Perm (Fin A.card)) ≃ Equiv.Perm (Fin A.card) :=
    { toFun := fun η => η ()
      invFun := fun ρ _ => ρ
      left_inv := fun η => by funext i; cases i; rfl
      right_inv := fun _ => rfl }
  exact h.trans (uniform_expect_equiv e f)

/-- Product expectations of arbitrary functions of disjoint relative orders. -/
theorem relativeOrder_expect_prod (A : I → Finset (Fin N))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (f : ∀ i, Equiv.Perm (Fin (A i).card) → ℝ) :
    expect (uniformPermutation N) (fun π => ∏ i, f i (relativeOrder (A i) π)) =
      ∏ i, expect (uniformPermutation N) (fun π => f i (relativeOrder (A i) π)) := by
  rw [relativeOrder_expect A hA (fun η => ∏ i, f i (η i))]
  simp_rw [relativeOrder_expect_single, expect_uniform]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [Fintype.card_pi, Nat.cast_prod]

theorem relativeOrder_surjective (A : Finset (Fin N)) :
    Function.Surjective (relativeOrder A) := by
  intro ρ
  let r := relativeOrder A (Equiv.refl _)
  let η : Unit → Equiv.Perm (Fin A.card) := fun _ => (orderTransform r).symm ρ
  let hA : ∀ i j : Unit, i ≠ j → Disjoint A A :=
    fun i j hij => False.elim (hij (Subsingleton.elim i j))
  refine ⟨(blockAction (fun _ : Unit => A) hA η).trans (Equiv.refl _), ?_⟩
  have h := relativeOrder_blockAction (fun _ : Unit => A) hA η (Equiv.refl _) ()
  exact h.trans ((orderTransform r).apply_symm_apply ρ)

def realizeRelativeOrder (A : Finset (Fin N)) (ρ : Equiv.Perm (Fin A.card)) :
    Permutation N := Classical.choose (relativeOrder_surjective A ρ)

@[simp] theorem relativeOrder_realize (A : Finset (Fin N)) (ρ : Equiv.Perm (Fin A.card)) :
    relativeOrder A (realizeRelativeOrder A ρ) = ρ :=
  Classical.choose_spec (relativeOrder_surjective A ρ)

/-- Independence for observables determined only by comparisons within their position sets. -/
theorem expect_prod_of_relativeOrder (A : I → Finset (Fin N))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (f : I → Permutation N → ℝ)
    (hf : ∀ i π σ, (∀ x ∈ A i, ∀ y ∈ A i, (π x < π y ↔ σ x < σ y)) →
      f i π = f i σ) :
    expect (uniformPermutation N) (fun π => ∏ i, f i π) =
      ∏ i, expect (uniformPermutation N) (f i) := by
  let g : ∀ i, Equiv.Perm (Fin (A i).card) → ℝ :=
    fun i ρ => f i (realizeRelativeOrder (A i) ρ)
  have hg (i : I) (π : Permutation N) : f i π = g i (relativeOrder (A i) π) := by
    apply hf
    apply (relativeOrder_eq_iff _ _ _).mp
    simp
  simpa only [← hg] using relativeOrder_expect_prod A hA g

/-- Exact integer counting form of the joint law; no divisibility is assumed. -/
theorem relativeOrder_fiber_card_mul (A : I → Finset (Fin N))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (η : ∀ i, Equiv.Perm (Fin (A i).card)) :
    Nat.card {π : Permutation N // (fun i => relativeOrder (A i) π) = η} *
      (∏ i, (A i).card.factorial) = N.factorial := by
  let Q := ∀ i, Equiv.Perm (Fin (A i).card)
  have h := relativeOrder_expect A hA (fun ρ => if ρ = η then (1 : ℝ) else 0)
  rw [expect_indicator, uniformPermutation, uniform_probability, expect_uniform] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have hQ : (Fintype.card Q : ℝ) ≠ 0 := by positivity
  have hP : (Fintype.card (Permutation N) : ℝ) ≠ 0 := by positivity
  have hc := (div_eq_div_iff hP hQ).mp h
  simp only [one_mul, ← Nat.card_eq_fintype_card] at hc
  have hc' : Nat.card {π : Permutation N // (fun i => relativeOrder (A i) π) = η} *
      Nat.card Q = Nat.card (Permutation N) := by exact_mod_cast hc
  have hQcard : Nat.card Q = ∏ i, (A i).card.factorial := by
    simp [Nat.card_eq_fintype_card, Q, Fintype.card_pi, Fintype.card_perm]
  have hPcard : Nat.card (Permutation N) = N.factorial := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  rwa [hQcard, hPcard] at hc'

theorem relativeOrderIndependence : Targets.RelativeOrderIndependence := by
  intro N d A hA τ
  have h := relativeOrder_expect A hA
    (fun η => if η = (fun i => relativeOrder (A i) (τ i)) then (1 : ℝ) else 0)
  have hevent (π : Permutation N) :
      (fun i => relativeOrder (A i) π) = (fun i => relativeOrder (A i) (τ i)) ↔
        ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, (π x < π y ↔ τ i x < τ i y) := by
    rw [funext_iff]
    simp only [relativeOrder_eq_iff]
  rw [expect_uniform] at h
  have hl : (fun π : Permutation N =>
      if (fun i => relativeOrder (A i) π) = (fun i => relativeOrder (A i) (τ i))
      then (1 : ℝ) else 0) =
      (fun π => if ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, (π x < π y ↔ τ i x < τ i y)
      then (1 : ℝ) else 0) := by
    funext π
    simp only [hevent]
  rw [hl] at h
  convert h using 1
  · unfold probability
    congr 1
    funext π
    split_ifs <;> rfl
  · simp [Fintype.card_pi, Fintype.card_perm, Fintype.card_fin, Nat.cast_prod,
      Finset.prod_inv_distrib, one_div]

end RiffleLowerV2.Ascent
