import RiffleUpperV2.ProfileUpper.FullCritical
import RiffleUpperV2.EmpiricalUpper.Main

/-! Public profile consequences of the proved physical empirical endpoint. -/
noncomputable section
open Filter
open scoped ENNReal
namespace RiffleUpperV2.ProfileUpper
open TimeProfile

/-- Source: thm:deterministic-upper-bound, with the exact frozen parameter order. -/
theorem bufferedUpper : Contracts.V1.P :=
  bufferedOfEmpirical EmpiricalUpper.empiricalUpper

/-- Source: thm:upper-critical-reduced, including the extended mixing bound. -/
theorem criticalTimeUpper : Contracts.V1.T :=
  criticalOfBuffered bufferedUpper

/-- The finite-horizon conclusion above the reduced extended critical time. -/
theorem criticalHorizonUpper {k : ℕ} (hk : 2 ≤ k) (μ : TimeLaw k)
    (cuts : ∀ N : ℕ, InfiniteCuts k N) (hFine : ArbitrarilyFineApproximation μ cuts)
    (t : ℝ) (ht : 0 ≤ t) (hcrit : criticalTime μ < ENNReal.ofReal t) :
    Tendsto (fun N => tv (physicalInverseLaw ((cuts N).take (horizonDepth N t)))
      (uniformPermutation N)) atTop (nhds 0) :=
  (criticalTimeUpper k hk μ cuts hFine).1 t ht hcrit

/-- Empty negativity sets retain critical time infinity; no finite mixing time
is presupposed by this limsup statement. -/
theorem mixingTimeUpper {k : ℕ} (hk : 2 ≤ k) (μ : TimeLaw k)
    (cuts : ∀ N : ℕ, InfiniteCuts k N) (hFine : ArbitrarilyFineApproximation μ cuts)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    limsup (fun N => mixingTime (cuts N) ε / ENNReal.ofReal (Real.log (N : ℝ))) atTop
      ≤ criticalTime μ :=
  (criticalTimeUpper k hk μ cuts hFine).2 ε hε hε1

/-- Source: cor:full-margin-critical-upper-bound. -/
theorem fullCriticalTimeUpper {k : ℕ} (hk : 2 ≤ k) (μ : TimeLaw k)
    (cuts : ∀ N : ℕ, InfiniteCuts k N) (hFine : ArbitrarilyFineApproximation μ cuts)
    (t : ℝ) (ht : 0 ≤ t) (hcrit : fullCriticalTime μ < ENNReal.ofReal t) :
    Tendsto (fun N => tv (physicalInverseLaw ((cuts N).take (horizonDepth N t)))
      (uniformPermutation N)) atTop (nhds 0) :=
  fullCriticalUpperOfBuffered bufferedUpper hk μ cuts hFine t ht hcrit

/-- Quantitative typical-environment bound for the entire joint cut array. -/
theorem randomEmpiricalBound : Contracts.V1.REmpiricalBound :=
  randomEmpiricalBoundOfEmpirical EmpiricalUpper.empiricalUpper

theorem randomEmpiricalUpper : Contracts.V1.REmpirical :=
  randomEmpiricalOfEmpirical EmpiricalUpper.empiricalUpper

/-- Source: cor:random-time-profile-upper-bound; the two typical events may be dependent. -/
theorem randomProfileUpper : Contracts.V1.RProfile :=
  randomProfileOfBuffered bufferedUpper

theorem randomUpper : Contracts.V1.R :=
  ⟨randomEmpiricalBound, randomEmpiricalUpper, randomProfileUpper⟩

end RiffleUpperV2.ProfileUpper
