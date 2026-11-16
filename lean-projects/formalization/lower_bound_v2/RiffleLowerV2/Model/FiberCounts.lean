import RiffleLowerV2.Model.FiniteLaws

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Model

/-- Permutations of positions that leave every key unchanged. -/
abbrev KeyStabilizer {N : ℕ} {W : Type*} (f : Fin N → W) :=
  {ρ : Permutation N // ∀ i, f (ρ i) = f i}

/-- Choosing an independent permutation in each key fiber describes its stabilizer exactly. -/
def keyStabilizerEquiv {N : ℕ} {W : Type*} (f : Fin N → W) :
    KeyStabilizer f ≃ (∀ w : W, Equiv.Perm {i : Fin N // f i = w}) where
  toFun ρ w := ρ.val.subtypeEquiv (fun i => by rw [ρ.property i])
  invFun η := ⟨Equiv.ofFiberEquiv η, Equiv.ofFiberEquiv_map η⟩
  left_inv ρ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    rfl
  right_inv η := by
    funext w
    apply Equiv.ext
    rintro ⟨i, hi⟩
    apply Subtype.ext
    subst w
    rfl

/-- The product includes unrealized keys, whose factors are 0! = 1. -/
theorem keyStabilizer_card {N : ℕ} {W : Type*} [Fintype W] (f : Fin N → W) :
    Fintype.card (KeyStabilizer f) =
      ∏ w : W, (Finset.univ.filter fun i => f i = w).card.factorial := by
  rw [Fintype.card_congr (keyStabilizerEquiv f), Fintype.card_pi]
  simp only [Fintype.card_perm, Fintype.card_subtype]

/-- A fiber of the map assigning keys to labels. -/
abbrev KeyAssignmentFiber {N : ℕ} {W : Type*} (f g : Fin N → W) :=
  {ρ : Permutation N // ∀ i, f (ρ i) = g i}

/-- Every realized assignment fiber is a translate of the key stabilizer. -/
def keyAssignmentFiberEquiv {N : ℕ} {W : Type*} (f g : Fin N → W)
    (τ : Permutation N) (hτ : ∀ i, f (τ i) = g i) :
    KeyAssignmentFiber f g ≃ KeyStabilizer f where
  toFun ρ := ⟨τ.symm.trans ρ.val, fun i => by
    change f (ρ.val (τ.symm i)) = f i
    rw [ρ.property, ← hτ, Equiv.apply_symm_apply]⟩
  invFun ρ := ⟨τ.trans ρ.val, fun i => by
    change f (ρ.val (τ i)) = g i
    rw [ρ.property, hτ]⟩
  left_inv ρ := by
    apply Subtype.ext
    ext i
    simp
  right_inv ρ := by
    apply Subtype.ext
    ext i
    simp

/-- Every supported key-assignment fiber has the same product-factorial size. -/
theorem keyAssignmentFiber_card {N : ℕ} {W : Type*} [Fintype W]
    (f g : Fin N → W) (τ : Permutation N) (hτ : ∀ i, f (τ i) = g i) :
    Fintype.card (KeyAssignmentFiber f g) =
      ∏ w : W, (Finset.univ.filter fun i => f i = w).card.factorial := by
  rw [Fintype.card_congr (keyAssignmentFiberEquiv f g τ hτ), keyStabilizer_card]

/-- Complete row words determine the actual dependent column-assignment sample. -/
theorem sample_eq_iff_rowWord {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω η : Sample cuts) : ω = η ↔ rowWord ω = rowWord η := by
  constructor
  · rintro rfl; rfl
  · intro h
    funext j
    apply Subtype.ext
    funext i
    have hi := congrArg (fun rows => (rows i).get j) h
    simpa only [rowWord_get, TimeProfile.sampleEntry] using hi

/-- The actual sample fiber agrees with the explicit key-assignment fiber. -/
def sampleRelabelFiberEquiv {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω η : Sample cuts) :
    {ρ : Permutation N // sampleRelabel cuts ρ ω = η} ≃
      KeyAssignmentFiber (rowWord ω) (rowWord η) :=
  (Equiv.refl (Permutation N)).subtypeEquiv (fun ρ => by
    rw [sample_eq_iff_rowWord, funext_iff]
    rfl)

/-- Equal full-word multisets are exactly enough to construct a row relabelling. -/
theorem exists_relabel_of_sortedWord_eq {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω η : Sample cuts) (h : sortedWord ω = sortedWord η) :
    ∃ ρ : Permutation N, sampleRelabel cuts ρ ω = η := by
  refine ⟨(stableSort η).symm.trans (stableSort ω), ?_⟩
  apply (sample_eq_iff_rowWord _ _).mpr
  funext i
  have hi := congrFun h ((stableSort η).symm i)
  simpa only [rowWord_relabel, Equiv.trans_apply, sortedWord, Equiv.apply_symm_apply] using hi

/-- Product of complete-word block factorials in every realized canonical sample fiber. -/
theorem sampleRelabel_fiber_card {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω η : Sample cuts) (h : sortedWord ω = sortedWord η) :
    Fintype.card {ρ : Permutation N // sampleRelabel cuts ρ ω = η} =
      ∏ w : Word k K, (Finset.univ.filter fun i => rowWord ω i = w).card.factorial := by
  obtain ⟨ρ, hρ⟩ := exists_relabel_of_sortedWord_eq ω η h
  rw [Fintype.card_congr (sampleRelabelFiberEquiv ω η)]
  have hr : ∀ i, rowWord ω (ρ i) = rowWord η i := by
    intro i
    exact congrArg (fun sample => rowWord sample i) hρ
  have hc := keyAssignmentFiber_card (rowWord ω) (rowWord η) ρ hr
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  convert hc using 1
  apply Finset.prod_congr rfl
  intro w _
  congr 2
  ext i
  simp

end RiffleLowerV2.Model
