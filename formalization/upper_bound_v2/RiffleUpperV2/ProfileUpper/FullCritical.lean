import RiffleUpperV2.ProfileUpper.AllMargins
import RiffleUpperV2.ProfileUpper.Critical

noncomputable section
open Set Filter
open scoped ENNReal
namespace RiffleUpperV2.ProfileUpper
open TimeProfile

theorem fullCriticalTime_empty {k : ℕ} (μ : TimeLaw k)
    (h : ¬ ∃ t : ℝ, 0 < t ∧ fullMargin μ t < 0) : fullCriticalTime μ = ⊤ := by
  have he : {t : ℝ | 0 < t ∧ fullMargin μ t < 0} = ∅ := by
    ext t
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro ht
    exact h ⟨t, ht⟩
  simp [fullCriticalTime, he]

theorem fineThresholdEquality {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {cuts : ∀ N : ℕ, InfiniteCuts k N} (hFine : ArbitrarilyFineApproximation μ cuts) :
    criticalTime μ = fullCriticalTime μ :=
  criticalTime_eq_full hk (fun _ ht => fine_scalarIntegrable hFine ht)

theorem fullCriticalUpperOfBuffered (hP : Contracts.V1.P) {k : ℕ} (hk : 2 ≤ k)
    (μ : TimeLaw k) (cuts : ∀ N : ℕ, InfiniteCuts k N)
    (hFine : ArbitrarilyFineApproximation μ cuts) (t : ℝ) (ht : 0 ≤ t)
    (hcrit : fullCriticalTime μ < ENNReal.ofReal t) :
    Tendsto (fun N => tv (physicalInverseLaw ((cuts N).take (horizonDepth N t)))
      (uniformPermutation N)) atTop (nhds 0) := by
  apply criticalTimeUpperOfBuffered hP hk μ cuts hFine t ht
  simpa only [fineThresholdEquality hk hFine] using hcrit

theorem eventuallyFiniteMixing {k : ℕ} {cuts : ∀ N : ℕ, InfiniteCuts k N}
    {ε t : ℝ} (hε : 0 < ε)
    (hconv : Tendsto (fun N => tv (physicalInverseLaw ((cuts N).take (horizonDepth N t)))
      (uniformPermutation N)) atTop (nhds 0)) :
    ∀ᶠ N in atTop, mixingTime (cuts N) ε < ⊤ := by
  filter_upwards [hconv.eventually (eventually_lt_nhds hε)] with N hN
  exact (mixingTime_le_of_tv (cuts N) hN.le).trans_lt (ENNReal.natCast_lt_top _)

end RiffleUpperV2.ProfileUpper
