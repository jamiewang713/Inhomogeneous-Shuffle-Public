import RiffleLowerV2.Ascent.FiniteProbability
import RiffleLowerV2.Ascent.Components

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Ascent

/-- Relabeling the two input positions is an involution of all permutations. -/
def swapPositions {N : ℕ} (i j : Fin N) : Permutation N ≃ Permutation N where
  toFun π := (Equiv.swap i j).trans π
  invFun π := (Equiv.swap i j).trans π
  left_inv π := by ext x; simp
  right_inv π := by ext x; simp

/-- Exact uniform comparison mean, proved by the swapping bijection. -/
theorem probability_uniform_ascent {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    probability (uniformPermutation N) (fun π => π i < π j) = 1/2 := by
  let P := uniformPermutation N
  let A := fun π : Permutation N => π i < π j
  have heq : probability P (fun π => π j < π i) = probability P A := by
    have h := uniform_probability_equiv (swapPositions i j)
      (fun π : Permutation N => π i < π j)
    simpa only [P, A, uniformPermutation, swapPositions, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_right] using h
  have hnot : (fun π : Permutation N => π j < π i) = (fun π => ¬ A π) := by
    funext π
    apply propext
    dsimp [A]
    have hne := π.injective.ne hij
    constructor
    · exact fun h => not_lt_of_ge h.le
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) hne.symm
  rw [hnot, probability_not] at heq
  change probability P A = 1/2
  linarith

theorem ascentCount_eq_sum {N : ℕ} (H : Finset (Fin N)) (π : Permutation N) :
    (ascentCount H π : ℝ) =
      ∑ e ∈ internalEdges H, if π (edgeLeft e) < π (edgeRight e) then (1 : ℝ) else 0 := by
  simp only [ascentCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Linearity suffices for the baseline; adjacent ascent indicators need not be independent. -/
theorem expect_ascentCount_uniform {N : ℕ} (H : Finset (Fin N)) :
    expect (uniformPermutation N) (fun π => (ascentCount H π : ℝ)) =
      ((internalEdges H).card : ℝ) / 2 := by
  simp_rw [ascentCount_eq_sum]
  rw [expect_sum]
  have h (e : Fin (N-1)) : expect (uniformPermutation N)
      (fun π => if π (edgeLeft e) < π (edgeRight e) then (1 : ℝ) else 0) = 1/2 := by
    rw [expect_indicator]
    apply probability_uniform_ascent
    intro heq
    have hv := congrArg (fun i : Fin N => i.val) heq
    dsimp [edgeLeft, edgeRight] at hv
    omega
  simp_rw [h]
  simp [div_eq_mul_inv]

end RiffleLowerV2.Ascent
