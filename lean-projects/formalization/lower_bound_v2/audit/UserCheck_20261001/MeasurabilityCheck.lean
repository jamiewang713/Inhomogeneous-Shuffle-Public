import RiffleLowerV2.Completed

/- Independent audit supplement. No production theorem or hypothesis is changed. -/
noncomputable section
open Set MeasureTheory TimeProfile

namespace RiffleLowerV2.UserCheck

/-- On a finite time interval, the proved scalar bounds make almost-everywhere
strong measurability sufficient for the endpoint's explicit integrability premise. -/
theorem scalarIntegrable_of_measurable
    {k : ℕ} (hk : 2 ≤ k) (μ : TimeLaw k) (P : BorelPartition k) (T : ℝ)
    (hc : ∀ i, AEStronglyMeasurable (cellMass μ P i) (volume.restrict (uIoc 0 T)))
    (ha : AEStronglyMeasurable (profileMaxCost μ) (volume.restrict (uIoc 0 T)))
    (hp : ∀ α ∈ Icc (2 : ℝ) 4,
      AEStronglyMeasurable (fun t => profilePsi μ t α) (volume.restrict (uIoc 0 T))) :
    ScalarIntegrable μ P T := by
  have bounded_integrable (f : ℝ → ℝ) (M : ℝ)
      (hf : AEStronglyMeasurable f (volume.restrict (uIoc 0 T)))
      (hbound : ∀ t, 0 ≤ f t ∧ f t ≤ M) : IntervalIntegrable f volume 0 T := by
    rw [intervalIntegrable_iff]
    apply IntegrableOn.of_bound (by simp [uIoc]) hf M
    exact ae_of_all _ fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound t).1] using (hbound t).2
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply bounded_integrable (cellMass μ P i) 1 (hc i)
    intro t
    exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
  · exact bounded_integrable (profileMaxCost μ) (Real.log (k : ℝ)) ha
      (ProfileTransfer.profileMaxCost_bounds hk μ)
  · intro α hα
    exact bounded_integrable (fun t => profilePsi μ t α) (4 * Real.log (k : ℝ))
      (hp α hα) (fun t => ProfileTransfer.profilePsi_bounds hk μ t hα)

/-- In this bounded setting, ScalarIntegrable is exactly the scalar
almost-everywhere measurability condition, not an additional analytic estimate. -/
theorem scalarIntegrable_iff_measurable
    {k : ℕ} (hk : 2 ≤ k) (μ : TimeLaw k) (P : BorelPartition k) (T : ℝ) :
    ScalarIntegrable μ P T ↔
      (∀ i, AEStronglyMeasurable (cellMass μ P i) (volume.restrict (uIoc 0 T))) ∧
      AEStronglyMeasurable (profileMaxCost μ) (volume.restrict (uIoc 0 T)) ∧
      ∀ α ∈ Icc (2 : ℝ) 4,
        AEStronglyMeasurable (fun t => profilePsi μ t α)
          (volume.restrict (uIoc 0 T)) := by
  constructor
  · intro h
    exact ⟨fun i => (h.1 i).aestronglyMeasurable_restrict_uIoc,
      h.2.1.aestronglyMeasurable_restrict_uIoc,
      fun α hα => (h.2.2 α hα).aestronglyMeasurable_restrict_uIoc⟩
  · rintro ⟨hc, ha, hp⟩
    exact scalarIntegrable_of_measurable hk μ P T hc ha hp

#print axioms scalarIntegrable_of_measurable
#print axioms scalarIntegrable_iff_measurable
#print axioms RiffleLowerV2.EmpiricalLower.empiricalCombined
#print axioms RiffleLowerV2.MacroscopicLower.macroscopicIntegrable
#print axioms RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto

end RiffleLowerV2.UserCheck
