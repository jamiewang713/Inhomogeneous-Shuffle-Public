import RiffleMain.MarginEvents
import RiffleUpperV2.ProfileUpper.Main
import RiffleMain.RandomLower.Forward

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology
namespace RiffleMain
open TimeProfile RiffleLowerV2 RiffleLowerV2.Targets

/-- The upper half at a fixed horizon, with empirical inputs supplied by the
weak-profile bridge rather than by extra assumptions in the final theorem. -/
theorem upperLimit_of_inputs {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {T g γ : ℝ} (hT : 0 < T) (hg : 0 < g) (hγ : 0 < γ)
    (P : BorelPartition k) (hI : ScalarIntegrable μ P T)
    (Q : ∀ N, PMF (HorizonCuts k N T))
    (herrors : Profile.IntervalErrorsInProbability μ T Q)
    (hgood : Profile.LocalGoodInProbability T Q g γ)
    (hmargin : RiffleUpperV2.reducedMargin μ T < 0) :
    Tendsto (fun N => tv (RiffleUpperV2.randomInverseLaw (Q N))
      (uniformPermutation N)) atTop (𝓝 0) := by
  let η := -RiffleUpperV2.reducedMargin μ T
  have hη : 0 < η := neg_pos.mpr hmargin
  have hneg := negativeMarginsInProbability hk hT hη P hI Q herrors
    (show RiffleUpperV2.reducedMargin μ T ≤ -η by dsimp [η]; linarith)
  obtain ⟨ρ, hρ, hbound⟩ := RiffleUpperV2.ProfileUpper.randomEmpiricalUpper
    k hk T (η/2) g γ hT (by positivity) hg hγ
  apply hbound ρ hρ le_rfl (fun N => horizonDepth N T)
    (fun N hN => by
      have h := (horizonDepth_error hN hT.le).1
      have hL := logScale_pos hN
      change 0 ≤ T - (horizonDepth N T : ℝ)/logScale N at h
      have hd := (div_le_iff₀ hL).mp (sub_nonneg.mp h)
      exact hd)
    Q
  have hjoint := Profile.probability_inter_tendsto_one Q _ _ hneg (hgood ρ hρ)
  apply Profile.probability_tendsto_one_mono Q _ _ hjoint
  apply Eventually.of_forall
  intro N cuts h
  obtain ⟨⟨hN, hm⟩, ⟨_, hl⟩⟩ := h
  refine ⟨hN, hm, ?_⟩
  exact localGood_shorten cuts (deckPos hN)
    (sub_nonneg.mp (horizonDepth_error hN hT.le).1) hl

/-- The lower half at a fixed horizon, including the common event needed
before averaging over all cut environments. -/
theorem lowerLimit_of_inputs {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {T g γ : ℝ} (hT : 0 < T) (hg : 0 < g) (hγ : 0 < γ)
    (P : BorelPartition k) (hI : ScalarIntegrable μ P T)
    (Q : ∀ N, PMF (HorizonCuts k N T))
    (herrors : Profile.IntervalErrorsInProbability μ T Q)
    (hgood : Profile.LocalGoodInProbability T Q g γ)
    (hmargin : 0 < RiffleUpperV2.reducedMargin μ T) :
    Tendsto (fun N => tv (RiffleUpperV2.randomInverseLaw (Q N))
      (uniformPermutation N)) atTop (𝓝 1) := by
  let η := RiffleUpperV2.reducedMargin μ T / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hκ : 0 < kappa0 η := by unfold kappa0 kappa; positivity
  let ρ := kappa0 η / (400*Real.log (k : ℝ))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hparams : ColdParameters k η g γ ρ := by
    refine ⟨hg, hγ, hρ, ?_⟩
    dsimp [ρ]
    calc
      2 * (kappa0 η / (400 * Real.log (k : ℝ))) * Real.log (k : ℝ) =
          kappa0 η / 200 := by field_simp [hlog.ne'] <;> ring
      _ ≤ kappa0 η / 100 := by linarith
  exact RandomLower.randomEmpiricalLower_tendsto k hk T η η hT hη hη g γ ρ Q
    (positiveMarginsInProbability hk hT hη P hI Q herrors hgood hparams
      (show 2*η ≤ RiffleUpperV2.reducedMargin μ T by dsimp [η]; linarith))

end RiffleMain
