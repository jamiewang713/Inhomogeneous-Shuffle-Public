import RiffleMain.Limits
import RiffleMain.Critical.Main
import RiffleMain.Profile.Main

/-! The current manuscript's Theorem 1.1, stated for finite marginals of the
whole random cut sequence. No independence between columns is imposed. -/
set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace RiffleMain
open TimeProfile RiffleLowerV2 RiffleLowerV2.Targets

theorem exists_profile_partition {k : ℕ} (hk : 2 ≤ k) : Nonempty (BorelPartition k) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨P, _⟩ := exists_regular_partition hk
    (chi := 1/(2*(k : ℝ))) (by positivity)
    (one_div_lt_one_div_of_lt hkR (by linarith))
  exact ⟨P⟩

theorem locallyScalarIntegrable_of_measurable {k : ℕ} (hk : 2 ≤ k)
    {μ : TimeLaw k} (hμ : Profile.MeasurableProfile μ) :
    Critical.LocallyScalarIntegrable μ := by
  obtain ⟨P⟩ := exists_profile_partition hk
  exact fun T _ => ⟨P, Profile.scalarIntegrable hk hμ P T⟩

/-- The two-sided fixed-horizon limit on the actual chronological forward law. -/
theorem main_fixed_horizon {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hμ : Profile.MeasurableProfile μ) (hnd : Profile.LocallyNondegenerate μ)
    {T : ℝ} (hT : 0 < T) (Q : ∀ N, PMF (HorizonCuts k N T))
    (hweak : Profile.WeaklyInProbability μ T Q)
    (hne : ENNReal.ofReal T ≠ RiffleUpperV2.criticalTime μ) :
    Tendsto (fun N => tv (RandomLower.randomForwardLaw (Q N)) (uniformPermutation N))
      atTop (𝓝 (if ENNReal.ofReal T < RiffleUpperV2.criticalTime μ then 1 else 0)) := by
  obtain ⟨herr, g, γ, hg, _, hγ, hgood⟩ := Profile.empirical_inputs hk Q hT hμ hnd hweak
  obtain ⟨P⟩ := exists_profile_partition hk
  have hI := Profile.scalarIntegrable hk hμ P T
  have hloc := locallyScalarIntegrable_of_measurable hk hμ
  split_ifs with hbelow
  · have hm := Critical.positive_below_critical_of_nondegenerate hk hloc hnd hT hbelow
    simpa only [RandomLower.tv_randomInverse_eq_forward] using
      lowerLimit_of_inputs hk hT hg hγ P hI Q herr hgood hm
  · have habove : RiffleUpperV2.criticalTime μ < ENNReal.ofReal T :=
      lt_of_le_of_ne (le_of_not_gt hbelow) hne.symm
    have hm := Critical.negative_above_critical hk hloc habove
    simpa only [RandomLower.tv_randomInverse_eq_forward] using
      upperLimit_of_inputs hk hT hg hγ P hI Q herr hgood hm

/-- The paper's weak-profile assumption for every fixed time horizon. `Q N K`
is the distribution of the first K cut vectors, with arbitrary joint dependence. -/
def RandomizedProfileLike {k : ℕ} (μ : Profile.NonnegativeTimeLaw k)
    (Q : ∀ N K : ℕ, PMF (Cuts k N K)) : Prop :=
  ∀ T : ℝ, 0 < T → Profile.WeaklyInProbability (Profile.extendNonnegativeProfile μ)
    T (fun N => Q N (horizonDepth N T))

/-- Critical time with the profile specified only on nonnegative times. -/
def criticalTime {k : ℕ} (μ : Profile.NonnegativeTimeLaw k) : ℝ≥0∞ :=
  RiffleUpperV2.criticalTime (Profile.extendNonnegativeProfile μ)

/-- Theorem 1.1, first assertion. The hypotheses are measurable profile,
local nondegeneracy, and weak profile convergence in probability. -/
theorem main {k : ℕ} (hk : 2 ≤ k) (μ : Profile.NonnegativeTimeLaw k)
    (hμ : Profile.NonnegativeMeasurableProfile μ)
    (hnd : Profile.LocallyNondegenerate (Profile.extendNonnegativeProfile μ))
    (Q : ∀ N K : ℕ, PMF (Cuts k N K)) (hQ : RandomizedProfileLike μ Q)
    (T : ℝ) (hT : 0 < T) (hne : ENNReal.ofReal T ≠ criticalTime μ) :
    Tendsto (fun N => tv (RandomLower.randomForwardLaw (Q N (horizonDepth N T)))
      (uniformPermutation N)) atTop
      (𝓝 (if ENNReal.ofReal T < criticalTime μ then 1 else 0)) :=
  main_fixed_horizon hk (Profile.extendNonnegativeProfile_measurable hμ)
    hnd hT (fun N => Q N (horizonDepth N T)) (hQ T hT) hne

/-- Theorem 1.1, finite critical time: both cutoff limits. -/
theorem cutoff {k : ℕ} (hk : 2 ≤ k) (μ : Profile.NonnegativeTimeLaw k)
    (hμ : Profile.NonnegativeMeasurableProfile μ)
    (hnd : Profile.LocallyNondegenerate (Profile.extendNonnegativeProfile μ))
    (Q : ∀ N K : ℕ, PMF (Cuts k N K)) (hQ : RandomizedProfileLike μ Q)
    (hfinite : criticalTime μ ≠ ⊤) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun N => tv (RandomLower.randomForwardLaw
      (Q N (horizonDepth N ((1-ε)*(criticalTime μ).toReal))))
      (uniformPermutation N)) atTop (𝓝 1) ∧
    Tendsto (fun N => tv (RandomLower.randomForwardLaw
      (Q N (horizonDepth N ((1+ε)*(criticalTime μ).toReal))))
      (uniformPermutation N)) atTop (𝓝 0) := by
  have hloc := locallyScalarIntegrable_of_measurable hk
    (Profile.extendNonnegativeProfile_measurable hμ)
  obtain ⟨hminus, hl, hu⟩ := Critical.cutoff_times hk hloc hfinite hε hε1
  change 0 < (1-ε)*(criticalTime μ).toReal at hminus
  change ENNReal.ofReal ((1-ε)*(criticalTime μ).toReal) < criticalTime μ at hl
  change criticalTime μ < ENNReal.ofReal ((1+ε)*(criticalTime μ).toReal) at hu
  have hC : 0 < (criticalTime μ).toReal := by
    have hp : 0 < 1-ε := by linarith
    change 0 < (1-ε)*(criticalTime μ).toReal at hminus
    exact (mul_pos_iff_of_pos_left hp).mp hminus
  have hplus : 0 < (1+ε)*(criticalTime μ).toReal := mul_pos (by linarith) hC
  constructor
  · simpa only [if_pos hl] using
      main hk μ hμ hnd Q hQ _ hminus hl.ne
  · simpa only [if_neg (not_lt_of_ge hu.le)] using
      main hk μ hμ hnd Q hQ _ hplus hu.ne.symm

/-- Theorem 1.1, infinite critical time: every finite positive horizon stays unmixed. -/
theorem infinite_critical {k : ℕ} (hk : 2 ≤ k) (μ : Profile.NonnegativeTimeLaw k)
    (hμ : Profile.NonnegativeMeasurableProfile μ)
    (hnd : Profile.LocallyNondegenerate (Profile.extendNonnegativeProfile μ))
    (Q : ∀ N K : ℕ, PMF (Cuts k N K)) (hQ : RandomizedProfileLike μ Q)
    (hinfinite : criticalTime μ = ⊤) (T : ℝ) (hT : 0 < T) :
    Tendsto (fun N => tv (RandomLower.randomForwardLaw (Q N (horizonDepth N T)))
      (uniformPermutation N)) atTop (𝓝 1) := by
  have hlt : ENNReal.ofReal T < criticalTime μ := by
    rw [hinfinite]
    exact ENNReal.ofReal_lt_top
  simpa only [if_pos hlt] using main hk μ hμ hnd Q hQ T hT hlt.ne

end RiffleMain
