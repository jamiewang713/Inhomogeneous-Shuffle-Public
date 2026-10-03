import RiffleUpperV2.Anchor.EqualFailure
import RiffleUpperV2.Shared.SideMass

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric RiffleUpperV2.Localization

theorem nonEqualProbability {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (j : Fin d) (a : Fin k) :
    (allowedCount cuts j (nonEqualDigits a) : ℝ) / n =
      leftProbability cuts j a + rightProbability cuts j a := by
  have he : (allowedCount cuts j (nonEqualDigits a) : ℝ) / n + digitProbability cuts j a = 1 := by
    unfold digitProbability
    rw [← add_div, ← Nat.cast_add, nonEqualCount]
    exact div_self (by positivity)
  have hs := digitSideProbabilityPartition cuts hn j a
  linarith

theorem sidePrefixMass_le_one {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (x : Prefix k d) (j : Fin x.1.val) : sidePrefixMass cuts x j ≤ 1 := by
  rw [sidePrefixMass_eq, ← prefixDigits_mass cuts hn]
  exact (cylinderMass_bounds cuts _).2

theorem equalCylinderMeans {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) :
    cylinderMean cuts R (prefixThenDigits x j (nonEqualDigits (x.2.get j))) =
      leftMean cuts R x j + rightMean cuts R x j ∧
    cylinderMean cuts (Finset.univ \ R)
      (singleDigits (prefixColumn x j) (nonEqualDigits (x.2.get j))) =
      ((n : ℝ) - R.card) * (leftProbability cuts (prefixColumn x j) (x.2.get j) +
        rightProbability cuts (prefixColumn x j) (x.2.get j)) := by
  constructor
  · unfold cylinderMean
    rw [prefixThenDigits_mass cuts hn, nonEqualProbability cuts hn]
    unfold leftMean rightMean
    ring
  · unfold cylinderMean
    rw [singleDigits_mass cuts hn, nonEqualProbability cuts hn,
      Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by simpa using Finset.card_le_univ R : R.card ≤ n)]

theorem equalCylinderMeans_lower {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {g : ℝ}
    (hg : Reserve R g) :
    g * leftMean cuts R x j ≤
      cylinderMean cuts R (prefixThenDigits x j (nonEqualDigits (x.2.get j))) ∧
    g * leftMean cuts R x j ≤ cylinderMean cuts (Finset.univ \ R)
      (singleDigits (prefixColumn x j) (nonEqualDigits (x.2.get j))) := by
  have hp : 0 ≤ leftProbability cuts (prefixColumn x j) (x.2.get j) := by
    unfold leftProbability; positivity
  have hq : 0 ≤ rightProbability cuts (prefixColumn x j) (x.2.get j) := by
    unfold rightProbability; positivity
  have ha := sidePrefixMass_nonneg cuts x j
  have ha1 := sidePrefixMass_le_one cuts hn x j
  have hM : (R.card : ℝ) ≤ n := by exact_mod_cast (by simpa using Finset.card_le_univ R : R.card ≤ n)
  have hbar : (R.card : ℝ) * sidePrefixMass cuts x j ≤ n := by
    calc
      _ ≤ (R.card : ℝ) * 1 := mul_le_mul_of_nonneg_left ha1 (Nat.cast_nonneg _)
      _ ≤ _ := by simpa only [mul_one] using hM
  have hl := leftMean_nonneg cuts R x j
  have hr := rightMean_nonneg cuts R x j
  constructor
  · rw [(equalCylinderMeans cuts hn R x j).1]
    nlinarith [hg.2.1]
  · rw [(equalCylinderMeans cuts hn R x j).2]
    have hreserve : g * n ≤ (n : ℝ) - R.card := by nlinarith [hg.2.2]
    have hsize : leftMean cuts R x j ≤
        (n : ℝ) * (leftProbability cuts (prefixColumn x j) (x.2.get j) +
          rightProbability cuts (prefixColumn x j) (x.2.get j)) := by
      unfold leftMean
      nlinarith [mul_le_mul_of_nonneg_right hbar hp]
    exact (mul_le_mul_of_nonneg_left hsize hg.1.le).trans (by
      nlinarith [mul_le_mul_of_nonneg_right hreserve (add_nonneg hp hq)])

/-- An actual exponentially small failure probability in the coincident-side
case, obtained from two fixed-column cylinders and the outside reserve. -/
theorem smoothingFailure_equal {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {g : ℝ}
    (hg : Reserve R g) :
    probability (fixedCountPMF cuts) (fun ω => ¬ equalGood cuts R x j ω) ≤
      2 * Real.exp (-RiffleLowerV2.chernoffConstant * g * leftMean cuts R x j) := by
  have hμ := equalCylinderMeans_lower cuts hn R x j hg
  have hc := RiffleLowerV2.Thinning.chernoffConstant_pos.le
  apply (equalGood_failure_raw cuts R x j).trans
  have hb := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hμ.1 (neg_nonpos.mpr hc))
  have hd := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hμ.2 (neg_nonpos.mpr hc))
  simp only [← mul_assoc] at hb hd
  linarith

end RiffleUpperV2.Anchor
