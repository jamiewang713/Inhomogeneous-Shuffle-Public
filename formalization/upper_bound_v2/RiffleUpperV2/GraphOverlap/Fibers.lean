import RiffleUpperV2.Shared.Model

/-! Arbitrary path-graph fibers. No shuffle realization of the graph is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.GraphOverlap
open RiffleLowerV2 RiffleLowerV2.Model

variable {N : ℕ}

def componentKey (G : PathEdges N) (i : Fin N) : Fin (N + 1) :=
  ⟨componentIndex G i, by
    have h := Finset.card_le_card (Finset.filter_subset
      (fun e : Fin (N-1) => e.val < i.val ∧ e ∉ G) Finset.univ)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    dsimp [componentIndex]
    omega⟩

@[simp] theorem componentKey_eq_iff (G : PathEdges N) (i j : Fin N) :
    componentKey G i = componentKey G j ↔ componentIndex G i = componentIndex G j :=
  Fin.ext_iff

/-- Unrealized component keys contribute the harmless factor `0! = 1`. -/
def componentFactorial (G : PathEdges N) : ℕ :=
  ∏ c : Fin (N + 1), (Finset.univ.filter fun i => componentKey G i = c).card.factorial

theorem componentFactorial_pos (G : PathEdges N) : 0 < componentFactorial G :=
  Finset.prod_pos (fun _ _ => Nat.factorial_pos _)

def componentFiberEquiv (G : PathEdges N) (σ : Permutation N)
    (hσ : BlockIncreasing G σ) :
    ComponentSortFiber G σ ≃
      KeyAssignmentFiber (componentKey G) (componentKey G ∘ σ.symm) where
  toFun π := ⟨π.val.symm, by
    intro i
    apply (componentKey_eq_iff G _ _).mpr
    have h := componentSort_preserves_component G π.val (σ.symm i)
    rw [π.property, Equiv.apply_symm_apply] at h
    exact h⟩
  invFun τ := ⟨τ.val.symm, by
    apply (componentSort_eq_iff G τ.val.symm σ hσ).mpr
    intro i
    have h := (componentKey_eq_iff G _ _).mp (τ.property (σ i))
    simpa only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply] using h⟩
  left_inv π := by apply Subtype.ext; exact Equiv.symm_symm π.val
  right_inv τ := by apply Subtype.ext; exact Equiv.symm_symm τ.val

theorem componentSort_fiber_card (G : PathEdges N) (σ : Permutation N)
    (hσ : BlockIncreasing G σ) :
    Fintype.card (ComponentSortFiber G σ) = componentFactorial G := by
  rw [Fintype.card_congr (componentFiberEquiv G σ hσ)]
  have hc := keyAssignmentFiber_card (componentKey G) (componentKey G ∘ σ.symm) σ.symm
    (fun _ => rfl)
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  convert hc using 1
  unfold componentFactorial
  apply Finset.prod_congr rfl
  intro c _
  congr 2
  ext i
  simp

theorem componentSort_fiber_card_eq (G : PathEdges N) (σ : Permutation N) :
    Fintype.card (ComponentSortFiber G σ) =
      if BlockIncreasing G σ then componentFactorial G else 0 := by
  split_ifs with hσ
  · exact componentSort_fiber_card G σ hσ
  · exact componentSort_fiber_card_of_not_increasing G σ hσ

end RiffleUpperV2.GraphOverlap
