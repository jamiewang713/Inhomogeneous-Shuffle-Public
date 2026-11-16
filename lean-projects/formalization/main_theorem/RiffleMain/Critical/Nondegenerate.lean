import RiffleMain.Critical.Continuity

set_option autoImplicit false

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RiffleMain.Critical
open TimeProfile RiffleLowerV2 RiffleUpperV2 RiffleUpperV2.ProfileUpper

/-- An a.e. lower bound on a whole horizon also bounds every subinterval integral. -/
theorem maxCost_lower_of_ae {k : ℕ} {μ : TimeLaw k} {P : BorelPartition k}
    {S T a : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) (hI : RiffleLowerV2.ScalarIntegrable μ P T)
    (hae : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), a ≤ profileMaxCost μ t) :
    a * (T-S) ≤ integratedMaxCost μ S T := by
  have hae0 : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) T → a ≤ profileMaxCost μ t :=
    (ae_restrict_iff' measurableSet_Icc).mp hae
  have haeST : ∀ᵐ t ∂(volume.restrict (Icc S T)), a ≤ profileMaxCost μ t := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hae0] with t ht
    intro hmem
    exact ht ⟨hS.trans hmem.1, hmem.2⟩
  have h := intervalIntegral.integral_mono_ae_restrict hST
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => a) volume S T)
    (scalar_restrict (hS.trans hST) hI.2.1 hS hST le_rfl) haeST
  simpa only [integratedMaxCost, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

theorem positiveIntervalCosts_of_nondegenerate {k : ℕ} {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) (hnd : LocallyNondegenerate μ) :
    PositiveIntervalCosts μ := by
  intro S T hS hST
  have hT : 0 < T := hS.trans_lt hST
  obtain ⟨P, hP⟩ := hI T hT
  obtain ⟨a, ha, hae⟩ := hnd T hT
  have h := maxCost_lower_of_ae hS hST.le hP hae
  exact (mul_pos ha (sub_pos.mpr hST)).trans_le h

theorem positive_below_critical_of_nondegenerate {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) (hnd : LocallyNondegenerate μ)
    {T : ℝ} (hT : 0 < T) (hcrit : ENNReal.ofReal T < criticalTime μ) :
    0 < reducedMargin μ T :=
  positive_below_critical hk hI (positiveIntervalCosts_of_nondegenerate hI hnd) hT hcrit

theorem positive_of_infinite_of_nondegenerate {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) (hnd : LocallyNondegenerate μ)
    (hcrit : criticalTime μ = ⊤) {T : ℝ} (hT : 0 < T) : 0 < reducedMargin μ T :=
  positive_of_critical_infinite hk hI (positiveIntervalCosts_of_nondegenerate hI hnd) hcrit hT

end RiffleMain.Critical
