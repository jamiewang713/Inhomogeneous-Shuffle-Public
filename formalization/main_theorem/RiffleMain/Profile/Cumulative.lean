import RiffleMain.Profile.Probability
import RiffleMain.Profile.ProfileTimeCut
import RiffleLowerV2.ProfileTransfer.Parameters

set_option autoImplicit false

noncomputable section
open Set MeasureTheory Filter
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

def empiricalCumulative {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (f : Simplex k → ℝ) (s : ℝ) : ℝ :=
  empiricalIntegral N (fun j => f (cuts.profile hN j)) 0 (min s (horizon N K))

def profileCumulative {k : ℕ} (μ : TimeLaw k) (f : Simplex k → ℝ) (s : ℝ) : ℝ :=
  ∫ t in 0..s, ∫ p, f p ∂(μ t : Measure (Simplex k))

/-- Every bounded nonnegative continuous spatial observable has its cumulative
integral converging in probability at each fixed time. -/
theorem cumulative_convergence {k : ℕ} {μ : TimeLaw k} {T : ℝ}
    (Q : ∀ N, PMF (Cuts k N (horizonDepth N T)))
    (hμ : MeasurableProfile μ) (hweak : WeaklyInProbability μ T Q)
    {f : Simplex k → ℝ} {M s : ℝ} (hf : Continuous f)
    (hb : ∀ p, 0 ≤ f p ∧ f p ≤ M) (hM : 0 ≤ M)
    (hs : s ∈ Icc 0 T) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => RiffleUpperV2.probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N,
        |empiricalCumulative cuts (by omega) f s - profileCumulative μ f s| < ε))
      atTop (nhds 1) := by
  let δ := ε / (8*(M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδbudget : 2*M*δ ≤ ε/4 := by
    have hh : δ*(8*(M+1)) = ε := by dsimp [δ]; field_simp
    nlinarith
  let test : Simplex k × ℝ → ℝ := fun z => f z.1 * timeCut s δ z.2
  have hc : Continuous test := (hf.comp continuous_fst).mul
    ((timeCut_continuous s δ).comp continuous_snd)
  have htest := hweak test hc.continuousOn (ε/2) (by positivity)
  apply probability_tendsto_one_mono Q _ _ htest
  filter_upwards [eventually_ge_atTop (transferThreshold M ε)] with N hlarge
  intro cuts hcuts
  obtain ⟨hN, he⟩ := hcuts
  refine ⟨hN, ?_⟩
  have hround := (transferThreshold_spec M hε).2 N hlarge
  have hemp := empirical_timeCut_error_clipped hN cuts hb hM hδ hs.1
  have hprof := profile_timeCut_error hμ hf hb hM hδ hs.1 hs.2
  let A := empiricalCumulative cuts (by omega) f s
  let B := empiricalTest cuts (by omega) test
  let C := profileTest μ T test
  let D := profileCumulative μ f s
  have htriangle := abs_sub_le A B D
  have htriangle' := abs_sub_le B C D
  change |A-B| ≤ M*(δ+1/logScale N) at hemp
  change |D-C| ≤ M*δ at hprof
  change |B-C| < ε/2 at he
  change |A-D| < ε
  rw [abs_sub_comm D C] at hprof
  have heq : M*(δ+1/logScale N) = M*δ+M/logScale N := by ring
  rw [heq] at hemp
  linarith

end RiffleMain.Profile
