import RiffleMain.Profile.SpatialContinuity

set_option autoImplicit false

noncomputable section
open Set MeasureTheory Filter
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

theorem uniform_psi_cumulative_convergence {k : ℕ} (hk : 2 ≤ k)
    {μ : TimeLaw k} {T : ℝ} (Q : ∀ N, PMF (Cuts k N (horizonDepth N T)))
    (hT : 0 ≤ T) (hμ : MeasurableProfile μ) (hweak : WeaklyInProbability μ T Q)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => RiffleUpperV2.probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N, ∀ θ ∈ Icc (2 : ℝ) 4, ∀ s ∈ Icc 0 T,
        |empiricalCumulative cuts (by omega) (fun p => psi p θ) s -
          profileCumulative μ (fun p => psi p θ) s| < ε)) atTop (nhds 1) := by
  let χ := ε/(8*(T+1))
  have hχ : 0 < χ := by dsimp [χ]; positivity
  have hbudget : 2*T*χ ≤ ε/4 := by
    have hh : χ*(8*(T+1)) = ε := by dsimp [χ]; field_simp
    nlinarith
  obtain ⟨δ, hδ, huc⟩ := psi_uniform_theta (k := k) hχ
  let grid := timeGrid 2 δ
  let A := fun q N (cuts : Cuts k N (horizonDepth N T)) =>
    ∃ hN : 2 ≤ N, ∀ s ∈ Icc 0 T,
      |empiricalCumulative cuts (by omega) (fun p => psi p (2+q)) s -
        profileCumulative μ (fun p => psi p (2+q)) s| < ε/2
  have hM : 0 ≤ 4*Real.log (k : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
  have hgrid : ∀ q ∈ grid,
      Tendsto (fun N => RiffleUpperV2.probability (Q N) (A q N)) atTop (nhds 1) := by
    intro q hq
    have hqI := timeGrid_mem (by norm_num : (0 : ℝ) ≤ 2) hδ hq
    have hθ : 2+q ∈ Icc (2 : ℝ) 4 := ⟨by linarith [hqI.1], by linarith [hqI.2]⟩
    exact uniform_cumulative_convergence Q hT hμ hweak (continuous_psi hθ)
      (fun p => psi_bounds hk p hθ) hM (by positivity)
  have hall := probability_tendsto_one_finset Q grid A hgrid
  apply probability_tendsto_one_mono Q _ _ hall
  apply Filter.Eventually.of_forall
  intro N cuts hcuts
  obtain ⟨hN, _⟩ := hcuts 0 (timeGrid_zero 2 δ)
  refine ⟨hN, ?_⟩
  intro θ hθ s hs
  have hθ2 : θ-2 ∈ Icc (0 : ℝ) 2 := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  obtain ⟨q, hq, hnear0, hnearδ⟩ := timeGrid_near hδ hθ2
  have hqI := timeGrid_mem (by norm_num : (0 : ℝ) ≤ 2) hδ hq
  have hθq : 2+q ∈ Icc (2 : ℝ) 4 := ⟨by linarith [hqI.1], by linarith [hqI.2]⟩
  have hd : |θ-(2+q)| < δ := by
    have heq : θ-(2+q) = θ-2-q := by ring
    rw [heq, abs_of_nonneg hnear0]
    exact hnearδ
  have hclose (p : Simplex k) : |psi p θ-psi p (2+q)| ≤ χ :=
    (huc θ (2+q) hθ hθq hd p).le
  obtain ⟨_, hc⟩ := hcuts q hq
  have hcerr := hc s hs
  have hemp := empiricalCumulative_spatial_error hN cuts hχ.le hclose hs
  have hprof := profileCumulative_spatial_error hμ (continuous_psi hθ)
    (continuous_psi hθq) (fun p => psi_bounds hk p hθ)
    (fun p => psi_bounds hk p hθq) hχ.le hclose hs
  let X := empiricalCumulative cuts (by omega) (fun p => psi p θ) s
  let Y := empiricalCumulative cuts (by omega) (fun p => psi p (2+q)) s
  let U := profileCumulative μ (fun p => psi p θ) s
  let V := profileCumulative μ (fun p => psi p (2+q)) s
  have htri := abs_sub_le X Y U
  have htri' := abs_sub_le Y V U
  change |X-Y| ≤ T*χ at hemp
  change |U-V| ≤ T*χ at hprof
  change |Y-V| < ε/2 at hcerr
  change |X-U| < ε
  rw [abs_sub_comm U V] at hprof
  linarith

/-- The uniform A/B conclusion of the manuscript's weak-profile lemma. -/
theorem weaklyInProbability_intervalErrors {k : ℕ} (hk : 2 ≤ k)
    {μ : TimeLaw k} {T : ℝ} (Q : ∀ N, PMF (Cuts k N (horizonDepth N T)))
    (hT : 0 < T) (hμ : MeasurableProfile μ) (hweak : WeaklyInProbability μ T Q) :
    IntervalErrorsInProbability μ T Q := by
  intro ε hε
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg
    (by exact_mod_cast (by omega : 1 ≤ k))
  have hA := uniform_cumulative_convergence Q hT.le hμ hweak continuous_maxCost
    (maxCost_bounds hk) hlog (show 0 < ε/2 by positivity)
  have hB := uniform_psi_cumulative_convergence hk Q hT.le hμ hweak
    (show 0 < ε/2 by positivity)
  have hboth := probability_inter_tendsto_one Q _ _ hA hB
  apply probability_tendsto_one_mono Q _ _ hboth
  apply Filter.Eventually.of_forall
  intro N cuts hcuts
  obtain ⟨⟨hN, hA⟩, ⟨_, hB⟩⟩ := hcuts
  have hST : horizon N (horizonDepth N T) ≤ T :=
    sub_nonneg.mp (horizonDepth_error hN hT.le).1
  refine ⟨hN, ?_, ?_⟩
  · intro r s hr hrs hs
    have hh := interval_error_of_cumulative hN cuts hμ continuous_maxCost (maxCost_bounds hk)
      hST (fun t ht => (hA t ht).le) hr hrs hs
    convert hh using 1 <;> first | rfl | ring
  · intro θ hθ r s hr hrs hs
    have hh := interval_error_of_cumulative hN cuts hμ (continuous_psi hθ)
      (fun p => psi_bounds hk p hθ) hST (fun t ht => (hB θ hθ t ht).le) hr hrs hs
    convert hh using 1 <;> first | rfl | ring

end RiffleMain.Profile
