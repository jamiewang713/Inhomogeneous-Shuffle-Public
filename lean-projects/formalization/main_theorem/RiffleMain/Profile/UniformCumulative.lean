import RiffleMain.Profile.FiniteGrid

set_option autoImplicit false

noncomputable section
open Set MeasureTheory Filter
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

theorem uniform_cumulative_convergence {k : ℕ} {μ : TimeLaw k} {T : ℝ}
    (Q : ∀ N, PMF (Cuts k N (horizonDepth N T)))
    (hT : 0 ≤ T) (hμ : MeasurableProfile μ) (hweak : WeaklyInProbability μ T Q)
    {f : Simplex k → ℝ} {M : ℝ} (hf : Continuous f)
    (hb : ∀ p, 0 ≤ f p ∧ f p ≤ M) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => RiffleUpperV2.probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N, ∀ s ∈ Icc 0 T,
        |empiricalCumulative cuts (by omega) f s - profileCumulative μ f s| < ε))
      atTop (nhds 1) := by
  let δ := ε/(8*(M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbudget : 2*M*δ ≤ ε/4 := by
    have hh : δ*(8*(M+1)) = ε := by dsimp [δ]; field_simp
    nlinarith
  let grid := timeGrid T δ
  let A := fun s N (cuts : Cuts k N (horizonDepth N T)) =>
    ∃ hN : 2 ≤ N,
      |empiricalCumulative cuts (by omega) f s - profileCumulative μ f s| < ε/2
  have hgrid : ∀ s ∈ grid,
      Tendsto (fun N => RiffleUpperV2.probability (Q N) (A s N)) atTop (nhds 1) := by
    intro s hs
    exact cumulative_convergence Q hμ hweak hf hb hM (timeGrid_mem hT hδ hs) (by positivity)
  have hall := probability_tendsto_one_finset Q grid A hgrid
  apply probability_tendsto_one_mono Q _ _ hall
  apply Filter.Eventually.of_forall
  intro N cuts hcuts
  obtain ⟨hN, _⟩ := hcuts 0 (timeGrid_zero T δ)
  refine ⟨hN, ?_⟩
  intro s hs
  obtain ⟨c, hc, hsc0, hscδ⟩ := timeGrid_near hδ hs
  obtain ⟨_, hcerr⟩ := hcuts c hc
  have hcI := timeGrid_mem hT hδ hc
  have hsample := empiricalCumulative_lipschitz hN cuts
    (fun p => by rw [abs_of_nonneg (hb p).1]; exact (hb p).2) hM hs.1 hcI.1
  have hlimit := profileCumulative_lipschitz hμ hf hb (s := c) (t := s)
  rw [abs_sub_comm c s] at hlimit
  have hdist : |s-c| ≤ δ := by rw [abs_of_nonneg hsc0]; exact hscδ.le
  have hsample' := hsample.trans (mul_le_mul_of_nonneg_right hdist hM)
  have hlimit' := hlimit.trans (mul_le_mul_of_nonneg_right hdist hM)
  have htriangle := abs_sub_le
    (empiricalCumulative cuts (by omega) f s)
    (empiricalCumulative cuts (by omega) f c) (profileCumulative μ f s)
  have htriangle' := abs_sub_le
    (empiricalCumulative cuts (by omega) f c)
    (profileCumulative μ f c) (profileCumulative μ f s)
  linarith

/-- Two cumulative estimates control every interval, including intervals whose
endpoints depend on the sampled environment. -/
theorem interval_error_of_cumulative {k N K : ℕ} (hN : 2 ≤ N)
    (cuts : Cuts k N K) {μ : TimeLaw k} (hμ : MeasurableProfile μ)
    {f : Simplex k → ℝ} {M T e : ℝ}
    (hf : Continuous f) (hb : ∀ p, 0 ≤ f p ∧ f p ≤ M)
    (hST : horizon N K ≤ T)
    (herr : ∀ s ∈ Icc 0 T,
      |empiricalCumulative cuts (by omega) f s - profileCumulative μ f s| ≤ e)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ horizon N K) :
    |empiricalIntegral N (fun j => f (cuts.profile (by omega) j)) r s -
      ∫ t in r..s, ∫ p, f p ∂(μ t : Measure (Simplex k))| ≤ 2*e := by
  have hrerr := herr r ⟨hr, hrs.trans (hs.trans hST)⟩
  have hserr := herr s ⟨hr.trans hrs, hs.trans hST⟩
  simp only [empiricalCumulative, min_eq_left (hrs.trans hs), min_eq_left hs,
    profileCumulative] at hrerr hserr
  let q := fun t => ∫ p, f p ∂(μ t : Measure (Simplex k))
  have hqb (t : ℝ) := scalar_integral_bounds (μ t) f
    (integrable_of_continuous_bounded (μ t) f hf hb) hb
  have hqi (a b : ℝ) : IntervalIntegrable q volume a b :=
    intervalIntegrable_of_measurable_bounded (measurable_profileIntegral hμ hf.measurable)
      (fun t => by rw [abs_of_nonneg (hqb t).1]; exact (hqb t).2) a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hqi 0 r) (hqi r s)
  have hesplit := empiricalIntegral_add N (fun j => f (cuts.profile (by omega) j)) 0 r s
  apply abs_le.mpr
  dsimp [q] at hsplit
  constructor <;> linarith [(abs_le.mp hrerr).1, (abs_le.mp hrerr).2,
    (abs_le.mp hserr).1, (abs_le.mp hserr).2]

end RiffleMain.Profile
