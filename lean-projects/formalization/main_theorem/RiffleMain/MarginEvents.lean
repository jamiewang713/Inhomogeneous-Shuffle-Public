import RiffleMain.Profile.Probability
import RiffleMain.Profile.Integrability
import RiffleMain.RandomLower.Basic
import RiffleUpperV2.Margins.ProfileMargin

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology
namespace RiffleMain
open TimeProfile RiffleLowerV2 RiffleLowerV2.Targets

/-- Negative macroscopic margins give the actual upper empirical predicate
with probability tending to one. The only random input is scalar convergence. -/
theorem negativeMarginsInProbability {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η)
    (P : BorelPartition k) (hI : ScalarIntegrable μ P T)
    (Q : ∀ N, PMF (HorizonCuts k N T))
    (herrors : Profile.IntervalErrorsInProbability μ T Q)
    (hmargin : RiffleUpperV2.reducedMargin μ T ≤ -η) :
    Tendsto (fun N => probability (Q N) (fun cuts => ∃ hN : 2 ≤ N,
      RiffleUpperV2.EmpiricalNegativeMargin N 0 cuts (deckPos hN) (η/2)))
      atTop (𝓝 1) := by
  have hboth := max_le_iff.mp hmargin
  apply Profile.probability_tendsto_one_mono Q _ _ (herrors (η/100) (by positivity))
  filter_upwards [eventually_ge_atTop
    (ProfileTransfer.transferThreshold (14*Real.log (k : ℝ)) η)] with N hlarge
  intro cuts h
  obtain ⟨hN, herr⟩ := h
  exact ⟨hN, RiffleUpperV2.Margins.profileToEmpiricalMargin_half hk hN hT hη
    hlarge P μ hI cuts herr hboth.1 hboth.2⟩

/-- Positive macroscopic margin gives one of the two lower empirical
alternatives. Both branches share the same event and fixed parameters. -/
theorem positiveMarginsInProbability {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {T η g γ ρ : ℝ} (hT : 0 < T) (hη : 0 < η)
    (P : BorelPartition k) (hI : ScalarIntegrable μ P T)
    (Q : ∀ N, PMF (HorizonCuts k N T))
    (herrors : Profile.IntervalErrorsInProbability μ T Q)
    (hgood : Profile.LocalGoodInProbability T Q g γ)
    (hparams : ColdParameters k η g γ ρ)
    (hmargin : 2*η ≤ RiffleUpperV2.reducedMargin μ T) :
    Tendsto (fun N => probability (Q N)
      (RandomLower.Admissible T η η g γ ρ N)) atTop (𝓝 1) := by
  have hrho := hparams.2.2.1
  have hevents := Profile.probability_inter_tendsto_one Q _ _
    (herrors (η/100) (by positivity)) (hgood ρ hrho)
  apply Profile.probability_tendsto_one_mono Q _ _ hevents
  filter_upwards [eventually_ge_atTop
    (ProfileTransfer.transferThreshold (14*Real.log (k : ℝ)) η)] with N hlarge
  intro cuts h
  obtain ⟨⟨hN, herr⟩, ⟨_, hlocal⟩⟩ := h
  have hm := ProfileTransfer.marginTransfer k N hk hN T hT P μ hI cuts
    (η/100) (by positivity) herr
  have hround := (RiffleUpperV2.Margins.profileMarginThreshold k hη).2 N hlarge
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hroundSmall : Real.log (k : ℝ)/logScale N ≤ η/4 := by
    have h := div_le_div_of_nonneg_right
      (show Real.log (k : ℝ) ≤ 14*Real.log (k : ℝ) by nlinarith)
      (logScale_pos hN).le
    exact h.trans hround
  refine ⟨hN, ?_⟩
  change 2*η ≤ max (macroBeta μ T) (macroLambda1 μ T) at hmargin
  rcases le_max_iff.mp hmargin with hb | hc
  · left
    have hb' := (abs_le.mp hm.1).1
    linarith
  · right
    refine ⟨hparams, hlocal, ?_⟩
    have hc' := (abs_le.mp hm.2).1
    linarith

/-- Restricting the right endpoint preserves the literal sliding-window
condition; in particular it removes the rounding gap at the last column. -/
theorem localGood_shorten {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    {g γ ρ r S T : ℝ} (hST : S ≤ T)
    (h : LocalGood cuts hN g γ ρ r T) : LocalGood cuts hN g γ ρ r S := by
  intro a ha hab
  exact h a ha (hab.trans hST)

end RiffleMain
