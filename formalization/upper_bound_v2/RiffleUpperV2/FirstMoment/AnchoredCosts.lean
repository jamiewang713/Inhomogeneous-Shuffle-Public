import RiffleUpperV2.FirstMoment.ClassAdapters

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization RiffleLowerV2.Thinning

/-- The selected digit probabilities are positive for every literal legal anchored prefix. -/
theorem legal_prefix_digits {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (default : Fin d → Fin k) (x : Prefix k d)
    (hx : Legal cuts R x) (j : Fin d) (hj : j.val < x.1.val) :
    0 < prob (cuts.profile hn j) (completePrefix default x j) := by
  have hm : prefixMass cuts x ≠ 0 := by
    intro hz
    change 0 < (R.card : ℝ)*prefixMass cuts x at hx
    simp [hz] at hx
  have hp : (∏ i, prefixColumnFraction cuts x i) ≠ 0 := by
    rwa [prefixColumnFraction_product]
  have hjne := (Finset.prod_ne_zero_iff.mp hp) j (Finset.mem_univ _)
  have hjpos := lt_of_le_of_ne (prefixColumnFraction_bounds cuts hn x j).1 (Ne.symm hjne)
  simpa [prefixColumnFraction, hj, completePrefix, Cuts.profile_prob] using hjpos

/-- Literal extension factorization in the full-population product; no row independence is used. -/
theorem prefixMass_extension {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (default : Fin d → Fin k) {v x : Prefix k d} (hvx : IsPrefix v x) :
    prefixMass cuts x = prefixMass cuts v *
      (∏ j ∈ empiricalPositions d 0 v.1.val x.1.val,
        prob (cuts.profile hn j) (completePrefix default x j)) := by
  classical
  change RiffleLowerV2.prefixMass cuts x = RiffleLowerV2.prefixMass cuts v * _
  rw [← prefixColumnFraction_product, ← prefixColumnFraction_product]
  rw [empiricalPositions, Finset.prod_filter, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hvlen := prefix_length_le hvx
  by_cases hjv : j.val < v.1.val
  · have hjx : j.val < x.1.val := lt_of_lt_of_le hjv hvlen
    have hd : v.2.get ⟨j.val,hjv⟩ = x.2.get ⟨j.val,hjx⟩ := by
      simpa [List.Vector.get, List.Vector.toList] using hvx.getElem (by simpa using hjv)
    simp [prefixColumnFraction, hjv, hjx, show ¬ v.1.val ≤ j.val by omega, hd]
  · by_cases hjx : j.val < x.1.val
    · simp [prefixColumnFraction, hjv, hjx, show v.1.val ≤ j.val by omega,
        completePrefix, Cuts.profile_prob]
    · simp [prefixColumnFraction, hjv, hjx]

theorem anchoredMean_extension {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (default : Fin d → Fin k) {v x : Prefix k d}
    (hvx : IsPrefix v x) :
    anchoredMean cuts R x = anchoredMean cuts R v *
      (∏ j ∈ empiricalPositions d 0 v.1.val x.1.val,
        prob (cuts.profile hn j) (completePrefix default x j)) := by
  unfold anchoredMean
  rw [prefixMass_extension cuts hn default hvx]
  ring

/-- Exact actual anchored mean decomposition into the recorded good and rare costs.
The normalization is the original N, even when the current deck has n rows. -/
theorem anchoredExactCostSplit {k n d N : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (default : Fin d → Fin k) {v x : Prefix k d}
    (hvx : IsPrefix v x) (hx : Legal cuts R x) (chi : ℝ) :
    meanExponent N cuts R x = meanExponent N cuts R v -
      goodCost N (cuts.profile hn) (empiricalPositions d 0 v.1.val x.1.val) chi
        (completePrefix default x) -
      exceptionalCost N (cuts.profile hn) (empiricalPositions d 0 v.1.val x.1.val) chi
        (completePrefix default x) := by
  have hv := legal_prefix cuts hn R hx hvx
  change Real.log (anchoredMean cuts R x)/logScale N =
    Real.log (anchoredMean cuts R v)/logScale N - _ - _
  rw [anchoredMean_extension cuts hn R default hvx]
  apply exactWordCostSplit _ _ _ chi _ hv
  intro j hj
  exact legal_prefix_digits cuts hn R default x hx j
    (by simpa [empiricalPositions] using (Finset.mem_filter.mp hj).2.2)

/-- Both exact selected costs are nonnegative on every actual legal extension. -/
theorem anchoredCosts_nonneg {k n d N : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    (default : Fin d → Fin k) (v x : Prefix k d) (hx : Legal cuts R x) (chi : ℝ) :
    0 ≤ goodCost N (cuts.profile hn) (empiricalPositions d 0 v.1.val x.1.val) chi
      (completePrefix default x) ∧
    0 ≤ exceptionalCost N (cuts.profile hn) (empiricalPositions d 0 v.1.val x.1.val) chi
      (completePrefix default x) := by
  have hlegal : ∀ j ∈ empiricalPositions d 0 v.1.val x.1.val,
      0 < prob (cuts.profile hn j) (completePrefix default x j) := by
    intro j hj
    exact legal_prefix_digits cuts hn R default x hx j
      (by simpa [empiricalPositions] using (Finset.mem_filter.mp hj).2.2)
  constructor
  · apply selectedCost_nonneg hN _ _ _
    intro j hj
    exact hlegal j (Finset.mem_sdiff.mp hj).1
  · apply selectedCost_nonneg hN _ _ _
    intro j hj
    exact hlegal j (Finset.mem_filter.mp hj).1

end RiffleUpperV2.FirstMoment
