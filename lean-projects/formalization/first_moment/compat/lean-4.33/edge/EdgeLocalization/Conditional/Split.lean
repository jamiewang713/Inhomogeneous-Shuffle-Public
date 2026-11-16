import EdgeLocalization.Conditional.Model
import EdgeLocalization.Collision.Matrix
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

/-! O.01–O.03 of the frozen occupancy-conditioning contract. -/

noncomputable section

namespace EdgeLocalization

theorem matrix_expectation_split {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K)
    (f : FixedMatrix N n → ℝ) :
    (matrixLaw n hn).expectation f =
      (matrixLaw (prefixCounts n hM) (fun j => hn (Fin.castLE hM j))).expectation
        (fun p =>
          (matrixLaw (suffixCounts n hM)
            (fun j => hn ⟨M + j.val, by have hj := j.isLt; omega⟩)).expectation
            (fun t => f ((splitMatrix N n hM).symm (p, t)))) := by
  classical
  let np := prefixCounts n hM
  let nt := suffixCounts n hM
  let hp : ∀ j, ∑ a, np j a = N := fun j => hn (Fin.castLE hM j)
  let ht : ∀ j, ∑ a, nt j a = N :=
    fun j => hn ⟨M + j.val, by have hj := j.isLt; omega⟩
  let e := splitMatrix N n hM
  have hc : Fintype.card (FixedMatrix N n) =
      Fintype.card (FixedMatrix N np) * Fintype.card (FixedMatrix N nt) := by
    exact (Fintype.card_congr e).trans (Fintype.card_prod _ _)
  have hw (p : FixedMatrix N np) (t : FixedMatrix N nt) :
      (matrixLaw n hn).weight (e.symm (p, t)) =
        (matrixLaw np hp).weight p * (matrixLaw nt ht).weight t := by
    simp [matrixLaw_uniform_weight, hc, Nat.cast_mul, mul_comm]
  change (matrixLaw n hn).expectation f =
    (matrixLaw np hp).expectation
      (fun p => (matrixLaw nt ht).expectation (fun t => f (e.symm (p, t))))
  unfold FiniteLaw.expectation
  calc
    _ = ∑ z : FixedMatrix N np × FixedMatrix N nt,
        (matrixLaw n hn).weight (e.symm z) * f (e.symm z) :=
      (e.symm.sum_comp (fun ω => (matrixLaw n hn).weight ω * f ω)).symm
    _ = ∑ p : FixedMatrix N np, ∑ t : FixedMatrix N nt,
        (matrixLaw n hn).weight (e.symm (p, t)) * f (e.symm (p, t)) :=
      Fintype.sum_prod_type _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [hw]
      ring

theorem tailCollisionFactor_suffix (N : ℕ) {K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hM : M ≤ K) :
    tailCollisionFactor N (suffixCounts n hM) 0 = tailCollisionFactor N n M := by
  classical
  unfold tailCollisionFactor
  have hs : (Finset.univ.filter (fun j : Fin (K - M) => 0 ≤ j.val)) =
      Finset.univ := by ext j; simp
  rw [hs]
  refine Finset.prod_bij
    (fun j _ => (⟨M + j.val, by have hj := j.isLt; omega⟩ : Fin K)) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
  · intro j _ l _ h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega
  · intro j hj
    have hjM := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val - M, by have hjK := j.isLt; omega⟩,
      Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp only
    omega
  · intro j _
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem prefix_occupancy_glue {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (x : Fin M → Fin k)
    (p : FixedMatrix N (prefixCounts n hM))
    (t : FixedMatrix N (suffixCounts n hM)) :
    occupancyCount N (rawRows n ((splitMatrix N n hM).symm (p, t))) (prefixWord x) =
      occupancyCount N (rawRows (prefixCounts n hM) p) (prefixWord x) := by
  classical
  let g := (splitMatrix N n hM).symm (p, t)
  have hc (j : Fin M) (i : Fin N) :
      (g (Fin.castLE hM j)).val i = (p j).val i := by
    exact congrArg
      (fun z : FixedMatrix N (prefixCounts n hM) ×
          FixedMatrix N (suffixCounts n hM) => (z.1 j).val i)
      ((splitMatrix N n hM).apply_symm_apply (p, t))
  have hm (i : Fin N) :
      prefixWord x <+: rawRow n g i ↔
        prefixWord x <+: rawRow (prefixCounts n hM) p i := by
    rw [prefixWord_prefix_rawRow_iff n hM x g i,
      prefixWord_prefix_rawRow_iff (prefixCounts n hM) (Nat.le_refl M) x p i]
    change (∀ j : Fin M, (g (Fin.castLE hM j)).val i = x j) ↔
      ∀ j : Fin M, (p j).val i = x j
    simp only [hc]
  unfold occupancyCount
  apply congrArg Finset.card
  ext i
  by_cases hi : i < N
  · simp only [occupied, Finset.mem_filter, Finset.mem_range, hi, true_and,
      rawRows, rowsOfLabels]
    exact hm ⟨i, hi⟩
  · simp only [occupied, Finset.mem_filter, Finset.mem_range, hi, false_and]

end EdgeLocalization
