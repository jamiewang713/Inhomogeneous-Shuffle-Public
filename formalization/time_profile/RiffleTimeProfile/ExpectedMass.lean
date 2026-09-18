import RiffleTimeProfile.FixedCountMoments
import RiffleTimeProfile.FixedCountModel

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TimeProfile

variable {k N K : ℕ}

private theorem prefixWeight_split_at (p : Fin K → Simplex k) (x : Fin K → Fin k)
    {w M : ℕ} (hwM : w ≤ M) :
    prefixWeight p x M = prefixWeight p x w *
      ∏ j ∈ positions K w M, prob (p j) (x j) := by
  classical
  have hs : positions K 0 M = positions K 0 w ∪ positions K w M := by
    ext j
    simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hd : Disjoint (positions K 0 w) (positions K w M) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    omega
  unfold prefixWeight
  rw [hs, Finset.prod_union hd]

private def prefixAllowed (x : Fin K → Fin k) (M : ℕ) (j : Fin K) : Finset (Fin k) :=
  if j.val < M then {x j} else Finset.univ

private theorem prefixAllowed_product (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (M : ℕ) :
    (∏ j, ∑ l ∈ prefixAllowed x M j, prob (p j) l) = prefixWeight p x M := by
  classical
  have hterm : ∀ j : Fin K, (∑ l ∈ prefixAllowed x M j, prob (p j) l) =
      if j.val < M then prob (p j) (x j) else 1 := by
    intro j
    by_cases hj : j.val < M
    · simp [prefixAllowed, hj]
    · simp [prefixAllowed, hj, sum_prob]
  simp only [hterm, prefixWeight, positions, Nat.zero_le, true_and,
    Finset.prod_filter]

private def sideAllowed (x : Fin K → Fin k) (j : Fin K) (D : Finset (Fin k))
    (h : Fin K) : Finset (Fin k) :=
  if h = j then D else if h.val < j.val then {x h} else Finset.univ

private theorem sideAllowed_product (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (j : Fin K) (D : Finset (Fin k)) :
    (∏ h, ∑ l ∈ sideAllowed x j D h, prob (p h) l) =
      prefixWeight p x j.val * (∑ l ∈ D, prob (p j) l) := by
  classical
  have hterm : ∀ h : Fin K, (∑ l ∈ sideAllowed x j D h, prob (p h) l) =
      (if h.val < j.val then prob (p h) (x h) else 1) *
        (if h = j then ∑ l ∈ D, prob (p j) l else 1) := by
    intro h
    by_cases hh : h = j
    · subst h
      simp [sideAllowed]
    · by_cases hlt : h.val < j.val
      · simp [sideAllowed, hh, hlt]
      · simp [sideAllowed, hh, hlt, sum_prob]
  simp only [hterm, Finset.prod_mul_distrib]
  congr 1
  · simp [prefixWeight, positions, Finset.prod_filter]
  · simp

private theorem boxRows_prefixAllowed (cuts : Cuts k N K) (x : Fin K → Fin k)
    (M : ℕ) (sample : ShuffleSample cuts) :
    boxRows (prefixAllowed x M) sample = prefixRows x M sample := by
  classical
  ext row
  simp only [boxRows, prefixRows, rowsSatisfying, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h j hj
    simpa [prefixAllowed, hj] using h j
  · intro h j
    by_cases hj : j.val < M
    · simpa [prefixAllowed, hj] using h j hj
    · simp [prefixAllowed, hj]

private theorem boxRows_sideAllowed (cuts : Cuts k N K) (x : Fin K → Fin k)
    (j : Fin K) (D : Finset (Fin k)) (sample : ShuffleSample cuts) :
    boxRows (sideAllowed x j D) sample =
      rowsSatisfying (sampleRow sample)
        (fun row => (∀ h, h.val < j.val → row h = x h) ∧ row j ∈ D) := by
  classical
  ext row
  simp only [boxRows, rowsSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    constructor
    · intro h' hlt
      have hne : h' ≠ j := by
        intro heq
        subst h'
        exact (lt_irrefl j.val) hlt
      simpa [sideAllowed, hne, hlt] using h h'
    · simpa [sideAllowed] using h j
  · rintro ⟨hprefix, hside⟩ h
    by_cases heq : h = j
    · subst h
      simpa [sideAllowed] using hside
    · by_cases hlt : h.val < j.val
      · simpa [sideAllowed, heq, hlt] using hprefix h hlt
      · simp [sideAllowed, heq, hlt]

/-- P05: every ambient cylinder has its exact product expectation, including zero mass. -/
theorem expected_prefix_count (cuts : Cuts k N K) (hN : 0 < N)
    (x : Fin K → Fin k) (M : ℕ) (hMK : M ≤ K) :
    (∫ sample : ShuffleSample cuts, ((prefixRows x M sample).card : ℝ)
      ∂fixedCountMeasure cuts) = prefixMass N (cuts.profile hN) x M := by
  classical
  have hbox := expected_box_count cuts hN (prefixAllowed x M)
  simp_rw [boxRows_prefixAllowed cuts x M] at hbox
  rw [prefixAllowed_product] at hbox
  exact hbox

/-- P05: the logarithm of expected cylinder size has the frozen ambient offset. -/
theorem cL_expected_mass_exponent (cuts : Cuts k N K) (hN : 2 ≤ N)
    (x : Fin K → Fin k) (b : ℝ) {w M : ℕ} (hwM : w ≤ M) (hMK : M ≤ K)
    (hlegal : LegalPrefix (cuts.profile (by omega)) x M) :
    Real.log (∫ sample : ShuffleSample cuts, ((prefixRows x M sample).card : ℝ)
      ∂fixedCountMeasure cuts) / logScale N =
      cL N (cuts.profile (by omega)) x b w M +
        (Real.log (∫ sample : ShuffleSample cuts, ((prefixRows x w sample).card : ℝ)
          ∂fixedCountMeasure cuts) / logScale N - b) := by
  rw [expected_prefix_count cuts (by omega) x M hMK,
    expected_prefix_count cuts (by omega) x w (le_trans hwM hMK)]
  exact cL_exact_mass_exponent N (cuts.profile (by omega)) x b hN hwM hMK hlegal

/-- P06: later columns are unrestricted in this left side piece. -/
theorem expected_left_side_count (cuts : Cuts k N K) (hN : 0 < N)
    (x : Fin K → Fin k) (j : Fin K) (w : ℕ) (hwj : w ≤ j.val) :
    (∫ sample : ShuffleSample cuts, ((leftSideRows x j sample).card : ℝ)
      ∂fixedCountMeasure cuts) =
      sideMass N (cuts.profile hN) x w leftProbability j := by
  classical
  let D := Finset.univ.filter (fun l : Fin k => l < x j)
  have hrows : ∀ sample : ShuffleSample cuts,
      boxRows (sideAllowed x j D) sample = leftSideRows x j sample := by
    intro sample
    rw [boxRows_sideAllowed]
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, leftSideRows]
  have hbox := expected_box_count cuts hN (sideAllowed x j D)
  simp_rw [hrows] at hbox
  rw [sideAllowed_product, prefixWeight_split_at _ _ hwj] at hbox
  simpa only [sideMass, prefixMass, leftProbability, D, mul_assoc] using hbox

/-- P06: the formula also covers an empty right side piece. -/
theorem expected_right_side_count (cuts : Cuts k N K) (hN : 0 < N)
    (x : Fin K → Fin k) (j : Fin K) (w : ℕ) (hwj : w ≤ j.val) :
    (∫ sample : ShuffleSample cuts, ((rightSideRows x j sample).card : ℝ)
      ∂fixedCountMeasure cuts) =
      sideMass N (cuts.profile hN) x w rightProbability j := by
  classical
  let D := Finset.univ.filter (fun l : Fin k => x j < l)
  have hrows : ∀ sample : ShuffleSample cuts,
      boxRows (sideAllowed x j D) sample = rightSideRows x j sample := by
    intro sample
    rw [boxRows_sideAllowed]
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, rightSideRows]
  have hbox := expected_box_count cuts hN (sideAllowed x j D)
  simp_rw [hrows] at hbox
  rw [sideAllowed_product, prefixWeight_split_at _ _ hwj] at hbox
  simpa only [sideMass, prefixMass, rightProbability, D, mul_assoc] using hbox

def expectedLeftMaximum (cuts : Cuts k N K) (x : Fin K → Fin k) (w v : ℕ) : ℝ :=
  ((positions K w v).sup (fun j => Real.toNNReal
    (∫ sample : ShuffleSample cuts, ((leftSideRows x j sample).card : ℝ)
      ∂fixedCountMeasure cuts)) : NNReal)

def expectedRightMaximum (cuts : Cuts k N K) (x : Fin K → Fin k) (w v : ℕ) : ℝ :=
  ((positions K w v).sup (fun j => Real.toNNReal
    (∫ sample : ShuffleSample cuts, ((rightSideRows x j sample).card : ℝ)
      ∂fixedCountMeasure cuts)) : NNReal)

def expectedCF (cuts : Cuts k N K) (x : Fin K → Fin k) (w v : ℕ) : WithBot ℝ :=
  min (logExponent N (Real.sqrt (expectedLeftMaximum cuts x w v)))
    (logExponent N (Real.sqrt (expectedRightMaximum cuts x w v)))

/-- P07: these are maxima of expectations, with the source empty-maximum convention. -/
theorem expected_side_maxima_eq (cuts : Cuts k N K) (hN : 2 ≤ N)
    (x : Fin K → Fin k) {w v : ℕ} (hwv : w ≤ v) (hvK : v ≤ K) :
    expectedLeftMaximum cuts x w v =
        sideMaximum N (cuts.profile (by omega)) x w v leftProbability ∧
      expectedRightMaximum cuts x w v =
        sideMaximum N (cuts.profile (by omega)) x w v rightProbability := by
  classical
  constructor
  · unfold expectedLeftMaximum sideMaximum
    congr 1
    apply Finset.sup_congr rfl
    intro j hj
    rw [expected_left_side_count cuts (by omega) x j w (Finset.mem_filter.mp hj).2.1]
  · unfold expectedRightMaximum sideMaximum
    congr 1
    apply Finset.sup_congr rfl
    intro j hj
    rw [expected_right_side_count cuts (by omega) x j w (Finset.mem_filter.mp hj).2.1]

/-- P07: the equality holds in the extended reals, including both zero-side cases. -/
theorem expected_cF_eq (cuts : Cuts k N K) (hN : 2 ≤ N)
    (x : Fin K → Fin k) {w v : ℕ} (hwv : w ≤ v) (hvK : v ≤ K) :
    expectedCF cuts x w v = cF N (cuts.profile (by omega)) x w v := by
  obtain ⟨hl, hr⟩ := expected_side_maxima_eq cuts hN x hwv hvK
  simp only [expectedCF, cF, hl, hr]

end TimeProfile
