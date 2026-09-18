import EdgeLocalization.Conditional.Counts

/-! Frozen occupancy-slice collision and internal-edge estimates O.06–O.07. -/

noncomputable section

namespace EdgeLocalization

theorem matrix_collisionPairs_occupancy_slice {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) (q : ℕ) :
    (matrixLaw n hn).expectation (fun ω =>
        if occupancyCount N (sortedRows n ω) (prefixWord x) = q then
          ((collisionPairs N (sortedRows n ω) (prefixWord x)).card : ℝ) else 0) =
      (Nat.choose q 2 : ℝ) * tailCollisionFactor N n M *
        (matrixLaw n hn).probability (fun ω =>
          occupancyCount N (sortedRows n ω) (prefixWord x) = q) := by
  classical
  let np := prefixCounts n hM
  let nt := suffixCounts n hM
  let hnp : ∀ j, ∑ a, np j a = N := fun j => hn (Fin.castLE hM j)
  let hnt : ∀ j, ∑ a, nt j a = N := by
    intro j
    simpa only [nt, suffixCounts] using hn ⟨M + j.val, by omega⟩
  let wp := matrixLaw np hnp
  let wt := matrixLaw nt hnt
  let glue := fun (p : FixedMatrix N np) (t : FixedMatrix N nt) =>
    (splitMatrix N n hM).symm (p, t)
  let z := fun ω : FixedMatrix N n =>
    occupancyCount N (sortedRows n ω) (prefixWord x)
  let zp := fun p : FixedMatrix N np =>
    occupancyCount N (rawRows np p) (prefixWord x)
  have hz (p : FixedMatrix N np) (t : FixedMatrix N nt) :
      z (glue p t) = zp p := by
    dsimp only [z, zp, glue, np]
    rw [sorted_occupancy_eq_raw, prefix_occupancy_glue]
  have hsplit (f : FixedMatrix N n → ℝ) :
      (matrixLaw n hn).expectation f =
        wp.expectation (fun p => wt.expectation (fun t => f (glue p t))) :=
    matrix_expectation_split n hn hM f
  have hprob : (matrixLaw n hn).probability (fun ω => z ω = q) =
      wp.probability (fun p => zp p = q) := by
    unfold FiniteLaw.probability
    rw [hsplit]
    apply congrArg wp.expectation
    funext p
    simp_rw [hz]
    by_cases hp : zp p = q
    · simp only [if_pos hp]
      exact wt.expectation_const 1
    · simp only [if_neg hp]
      exact wt.expectation_const 0
  have hinner (p : FixedMatrix N np) :
      wt.expectation (fun t => if z (glue p t) = q then
        ((collisionPairs N (sortedRows n (glue p t)) (prefixWord x)).card : ℝ) else 0) =
      if zp p = q then (Nat.choose q 2 : ℝ) * tailCollisionFactor N n M else 0 := by
    simp_rw [hz]
    by_cases hp : zp p = q
    · simp only [if_pos hp]
      have hc : wt.expectation (fun t =>
          ((collisionPairs N (sortedRows n (glue p t)) (prefixWord x)).card : ℝ)) =
          (Nat.choose (zp p) 2 : ℝ) * tailCollisionFactor N n M :=
        tail_expected_collisionPairs_given_prefix_array n hn hM x p
      rw [hc, hp]
    · simp only [if_neg hp]
      exact wt.expectation_const 0
  calc
    _ = wp.expectation (fun p => wt.expectation (fun t =>
        if z (glue p t) = q then
          ((collisionPairs N (sortedRows n (glue p t)) (prefixWord x)).card : ℝ)
        else 0)) := by exact hsplit _
    _ = wp.expectation (fun p =>
        if zp p = q then (Nat.choose q 2 : ℝ) * tailCollisionFactor N n M else 0) := by
      apply congrArg wp.expectation
      funext p
      exact hinner p
    _ = (Nat.choose q 2 : ℝ) * tailCollisionFactor N n M *
        wp.probability (fun p => zp p = q) := by
      unfold FiniteLaw.probability FiniteLaw.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : zp p = q
      · simp only [if_pos hp, mul_one]
        ring
      · simp only [if_neg hp, mul_zero]
    _ = _ := by rw [hprob]

theorem matrix_internal_edges_occupancy_slice {N K k M : ℕ}
    (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N)
    (hM : M ≤ K) (x : Fin M → Fin k) (q : ℕ) :
    (matrixLaw n hn).expectation (fun ω =>
        if occupancyCount N (sortedRows n ω) (prefixWord x) = q then
          (edgeCount N (sortedRows n ω) (prefixWord x) : ℝ) else 0) ≤
      (Nat.choose q 2 : ℝ) * tailCollisionFactor N n M *
        (matrixLaw n hn).probability (fun ω =>
          occupancyCount N (sortedRows n ω) (prefixWord x) = q) := by
  calc
    _ ≤ (matrixLaw n hn).expectation (fun ω =>
        if occupancyCount N (sortedRows n ω) (prefixWord x) = q then
          ((collisionPairs N (sortedRows n ω) (prefixWord x)).card : ℝ) else 0) := by
      apply (matrixLaw n hn).expectation_mono
      intro ω
      split_ifs
      · exact_mod_cast internalEdges_card_le_collisionPairs
          N (sortedRows n ω) (prefixWord x)
      · exact le_refl 0
    _ = _ := matrix_collisionPairs_occupancy_slice n hn hM x q

end EdgeLocalization
