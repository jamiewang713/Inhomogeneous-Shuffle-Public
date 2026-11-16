import RiffleLowerV2.Model.GraphSorting
import RiffleLowerV2.Model.FiberCounts

/-! Exact supported and unsupported fibers of component normalization. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Model

variable {N : ℕ}

/-- A permutation is in increasing order on every path component. -/
def BlockIncreasing (G : PathEdges N) (σ : Permutation N) : Prop :=
  ∀ i j : Fin N, i < j → componentIndex G i = componentIndex G j → σ i < σ j

theorem componentSort_blockIncreasing (G : PathEdges N) (π : Permutation N) :
    BlockIncreasing G (componentSort G π) := by
  intro i j hij heq
  exact componentSort_increasing G π hij heq

/-- A supported output is determined by the label set assigned to each component. -/
theorem componentSort_eq_iff (G : PathEdges N) (π σ : Permutation N)
    (hσ : BlockIncreasing G σ) :
    componentSort G π = σ ↔
      ∀ i, componentIndex G (π.symm (σ i)) = componentIndex G i := by
  constructor
  · intro heq i
    rw [← heq]
    exact componentSort_preserves_component G π i
  · intro h
    let c := componentIndex G
    let p := σ.trans π.symm
    have hp (i : Fin N) : c (p i) = c i := h i
    have hv (i : Fin N) : π (p i) = σ i := by simp [p]
    have hsort : p = Tuple.sort (fun i => (toLex (c i, π i) : ℕ ×ₗ Fin N)) := by
      apply Tuple.eq_sort_iff.mpr
      constructor
      · intro i j hij
        change toLex (c (p i), π (p i)) ≤ (toLex (c (p j), π (p j)) : ℕ ×ₗ Fin N)
        rw [hp, hp, hv, hv]
        apply Prod.Lex.toLex_le_toLex.mpr
        rcases (componentIndex_monotone G hij).lt_or_eq with hlt | heq
        · exact Or.inl hlt
        · apply Or.inr
          refine ⟨heq, ?_⟩
          rcases hij.eq_or_lt with hsame | hlt
          · simp [hsame]
          · exact (hσ i j hlt heq).le
      · intro i j hij heq
        have heq' : π (p i) = π (p j) := congrArg (fun v : ℕ ×ₗ Fin N => (ofLex v).2) heq
        exact False.elim (hij.ne (p.injective (π.injective heq')))
    unfold componentSort
    rw [← hsort]
    apply Equiv.ext
    intro i
    exact hv i

/-- The literal finite preimage under component sorting. -/
abbrev ComponentSortFiber (G : PathEdges N) (σ : Permutation N) :=
  {π : Permutation N // componentSort G π = σ}

theorem componentSort_fiber_card_of_not_increasing (G : PathEdges N) (σ : Permutation N)
    (hσ : ¬BlockIncreasing G σ) : Fintype.card (ComponentSortFiber G σ) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun π => hσ ?_⟩
  rw [← π.property]
  exact componentSort_blockIncreasing G π.val

/-- Inversion turns component preimages into assignments of full words to original labels. -/
def shuffleComponentFiberEquiv {k K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω : Sample cuts) (σ : Permutation N) (hσ : BlockIncreasing (shuffleEdges ω) σ) :
    ComponentSortFiber (shuffleEdges ω) σ ≃
      KeyAssignmentFiber (sortedWord ω) (sortedWord ω ∘ σ.symm) where
  toFun π := ⟨π.val.symm, by
    intro i
    apply (shuffle_componentIndex_eq_iff ω _ _).mp
    have h := componentSort_preserves_component (shuffleEdges ω) π.val (σ.symm i)
    rw [π.property, Equiv.apply_symm_apply] at h
    exact h⟩
  invFun τ := ⟨τ.val.symm, by
    apply (componentSort_eq_iff (shuffleEdges ω) τ.val.symm σ hσ).mpr
    intro i
    apply (shuffle_componentIndex_eq_iff ω _ _).mpr
    have h := τ.property (σ i)
    simpa only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply] using h⟩
  left_inv π := by apply Subtype.ext; exact Equiv.symm_symm π.val
  right_inv τ := by apply Subtype.ext; exact Equiv.symm_symm τ.val

/-- Every supported fiber has the product of the full-word block factorials. -/
theorem shuffle_componentSort_fiber_card {k K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω : Sample cuts) (σ : Permutation N) (hσ : BlockIncreasing (shuffleEdges ω) σ) :
    Fintype.card (ComponentSortFiber (shuffleEdges ω) σ) =
      ∏ w : Word k K, (Finset.univ.filter fun i => sortedWord ω i = w).card.factorial := by
  rw [Fintype.card_congr (shuffleComponentFiberEquiv ω σ hσ)]
  have hc := keyAssignmentFiber_card (sortedWord ω) (sortedWord ω ∘ σ.symm) σ.symm
    (fun _ => rfl)
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  convert hc using 1
  apply Finset.prod_congr rfl
  intro w _
  congr 2
  ext i
  simp

/-- Total fiber formula, including permutations that cannot be normalized outputs. -/
theorem shuffle_componentSort_fiber_card_eq {k K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω : Sample cuts) (σ : Permutation N) :
    Fintype.card (ComponentSortFiber (shuffleEdges ω) σ) =
      if BlockIncreasing (shuffleEdges ω) σ then
        ∏ w : Word k K, (Finset.univ.filter fun i => sortedWord ω i = w).card.factorial
      else 0 := by
  split_ifs with hσ
  · exact shuffle_componentSort_fiber_card ω σ hσ
  · exact componentSort_fiber_card_of_not_increasing (shuffleEdges ω) σ hσ

/-- The support predicate is exactly stable tie order in the full-word blocks. -/
theorem shuffle_blockIncreasing_iff {k K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω : Sample cuts) (σ : Permutation N) :
    BlockIncreasing (shuffleEdges ω) σ ↔
      ∀ i j : Fin N, i < j → sortedWord ω i = sortedWord ω j → σ i < σ j := by
  unfold BlockIncreasing
  simp only [shuffle_componentIndex_eq_iff]

end RiffleLowerV2.Model
