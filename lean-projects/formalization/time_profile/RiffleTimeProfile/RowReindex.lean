import RiffleTimeProfile.ExpectedMass

/-!
P08: row permutations preserve occupancies, even when chosen from the sample.
This concerns cardinalities and does not assert preservation of the sample law.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TimeProfile

variable {k N K : ℕ}

/-- P08: any predicate on complete row words has permutation-invariant occupancy. -/
theorem rowCount_reindex (rows : Fin N → Fin K → Fin k)
    (B : (Fin K → Fin k) → Prop) (sigma : Equiv.Perm (Fin N)) :
    rowCount (fun i => rows (sigma i)) B = rowCount rows B := by
  classical
  simp only [rowCount, rowsSatisfying, Finset.card_filter]
  exact Equiv.sum_comp sigma (fun i => if B (rows i) then 1 else 0)

/-- P08: the permutation may depend on the entire sample. -/
theorem sample_rowCount_reindex (cuts : Cuts k N K)
    (B : (Fin K → Fin k) → Prop)
    (sigma : ShuffleSample cuts → Equiv.Perm (Fin N)) (sample : ShuffleSample cuts) :
    rowCount (fun i => sampleRow sample (sigma sample i)) B =
      rowCount (sampleRow sample) B :=
  rowCount_reindex (sampleRow sample) B (sigma sample)

/-- P08: equality of the counted random variables transfers their expectations. -/
theorem expected_rowCount_reindex (cuts : Cuts k N K)
    (B : (Fin K → Fin k) → Prop)
    (sigma : ShuffleSample cuts → Equiv.Perm (Fin N)) :
    (∫ sample, (rowCount (fun i => sampleRow sample (sigma sample i)) B : ℝ)
      ∂fixedCountMeasure cuts) =
      ∫ sample, (rowCount (sampleRow sample) B : ℝ) ∂fixedCountMeasure cuts := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun sample =>
    congrArg (fun n : ℕ => (n : ℝ)) (sample_rowCount_reindex cuts B sigma sample)

/-- P08: source prefix expectations are unchanged after any sorting permutation. -/
theorem expected_prefix_count_reindex (cuts : Cuts k N K) (hN : 0 < N)
    (x : Fin K → Fin k) (M : ℕ) (hMK : M ≤ K)
    (sigma : ShuffleSample cuts → Equiv.Perm (Fin N)) :
    (∫ sample, (rowCount (fun i => sampleRow sample (sigma sample i))
      (fun word => ∀ j : Fin K, j.val < M → word j = x j) : ℝ)
      ∂fixedCountMeasure cuts) = prefixMass N (cuts.profile hN) x M := by
  rw [expected_rowCount_reindex]
  simpa only [rowCount, prefixRows] using expected_prefix_count cuts hN x M hMK

/-- P08: the left side keeps its free suffix after sample-dependent reindexing. -/
theorem expected_left_side_count_reindex (cuts : Cuts k N K) (hN : 0 < N)
    (x : Fin K → Fin k) (j : Fin K) (w : ℕ) (hwj : w ≤ j.val)
    (sigma : ShuffleSample cuts → Equiv.Perm (Fin N)) :
    (∫ sample, (rowCount (fun i => sampleRow sample (sigma sample i))
      (fun word => (∀ h : Fin K, h.val < j.val → word h = x h) ∧ word j < x j) : ℝ)
      ∂fixedCountMeasure cuts) =
      sideMass N (cuts.profile hN) x w leftProbability j := by
  rw [expected_rowCount_reindex]
  simpa only [rowCount, leftSideRows] using expected_left_side_count cuts hN x j w hwj

/-- P08: the same unconditional expectation identity holds for the right side. -/
theorem expected_right_side_count_reindex (cuts : Cuts k N K) (hN : 0 < N)
    (x : Fin K → Fin k) (j : Fin K) (w : ℕ) (hwj : w ≤ j.val)
    (sigma : ShuffleSample cuts → Equiv.Perm (Fin N)) :
    (∫ sample, (rowCount (fun i => sampleRow sample (sigma sample i))
      (fun word => (∀ h : Fin K, h.val < j.val → word h = x h) ∧ x j < word j) : ℝ)
      ∂fixedCountMeasure cuts) =
      sideMass N (cuts.profile hN) x w rightProbability j := by
  rw [expected_rowCount_reindex]
  simpa only [rowCount, rightSideRows] using expected_right_side_count cuts hN x j w hwj

end TimeProfile
