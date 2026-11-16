import RiffleUpperV2.Anchor.EqualCylinder

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric RiffleLowerV2.Thinning

/-- The two actual lower-tail failures, before deterministic scale comparison. -/
theorem equalGood_failure_raw {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) :
    probability (fixedCountPMF cuts) (fun ω => ¬ equalGood cuts R x j ω) ≤
      Real.exp (-RiffleLowerV2.chernoffConstant * cylinderMean cuts R
        (prefixThenDigits x j (nonEqualDigits (x.2.get j)))) +
      Real.exp (-RiffleLowerV2.chernoffConstant * cylinderMean cuts (Finset.univ \ R)
        (singleDigits (prefixColumn x j) (nonEqualDigits (x.2.get j)))) := by
  let μ := cylinderMean cuts R (prefixThenDigits x j (nonEqualDigits (x.2.get j)))
  let ν := cylinderMean cuts (Finset.univ \ R)
    (singleDigits (prefixColumn x j) (nonEqualDigits (x.2.get j)))
  have hb : probability (fixedCountPMF cuts)
      (fun ω => ((equalSampleRows R x j ω).card : ℝ) ≤ μ/2) ≤ Real.exp (-RiffleLowerV2.chernoffConstant * μ) := by
    have h := (anchorCylinderTail cuts R (prefixThenDigits x j (nonEqualDigits (x.2.get j)))
      (t := 1) (by norm_num)).2
    simpa only [RiffleUpperV2.probability, RiffleUpperV2.fixedCountPMF, cylinderCount, ← equalSampleRows_eq_cylinder cuts, μ] using h
  have hc : probability (fixedCountPMF cuts)
      (fun ω => ((equalReserveRows R x j ω).card : ℝ) ≤ ν/2) ≤ Real.exp (-RiffleLowerV2.chernoffConstant * ν) := by
    have h := (anchorCylinderTail cuts (Finset.univ \ R)
      (singleDigits (prefixColumn x j) (nonEqualDigits (x.2.get j)))
      (t := 1) (by norm_num)).2
    simpa only [RiffleUpperV2.probability, RiffleUpperV2.fixedCountPMF, cylinderCount, ← equalReserveRows_eq_cylinder cuts, ν] using h
  apply le_trans (probability_mono (fixedCountPMF cuts) (B := fun ω =>
    ((equalSampleRows R x j ω).card : ℝ) ≤ μ/2 ∨ ((equalReserveRows R x j ω).card : ℝ) ≤ ν/2) ?_)
    ((probability_union_le (fixedCountPMF cuts) _ _).trans (add_le_add hb hc))
  intro ω h
  change ¬ (μ/2 ≤ _ ∧ ν/2 ≤ _) at h
  rcases not_and_or.mp h with h | h
  · exact Or.inl (not_le.mp h).le
  · exact Or.inr (not_le.mp h).le

end RiffleUpperV2.Anchor
