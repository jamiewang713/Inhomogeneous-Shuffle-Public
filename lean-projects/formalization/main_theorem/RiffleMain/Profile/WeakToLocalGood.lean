import RiffleMain.Profile.LocalGoodBounds

set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Filter
open scoped BigOperators
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

theorem localGood_of_cumulative {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) {μ : TimeLaw k} (hμ : MeasurableProfile μ)
    {T aT ρ : ℝ} (haT : 0 < aT) (hρ : 0 < ρ)
    (hlower : ∀ᵐ t ∂volume.restrict (Icc 0 T), aT ≤ profileMaxCost μ t)
    (herr : ∀ t ∈ Icc 0 T,
      |empiricalCumulative cuts (by omega) maxCost t - profileCumulative μ maxCost t| ≤ aT*ρ/16)
    (hround : 2*Real.log (k : ℝ)/logScale N ≤ aT*ρ/8) :
    TimeProfile.LocalGood cuts (by omega) (goodThreshold k aT)
      (aT/(4*Real.log (k : ℝ))) ρ 0 T := by
  classical
  intro a ha hwindow
  have hL := logScale_pos hN
  have hM : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hlo := maxCost_interval_lower hk hμ hlower ha (by linarith : a ≤ a+ρ) hwindow
  have herr' := clipped_maxCost_interval_error hk hN cuts hμ herr
    (show a ∈ Icc 0 T from ⟨ha, by linarith⟩)
    (show a+ρ ∈ Icc 0 T from ⟨by linarith, hwindow⟩)
  have hupper := maxCost_interval_upper hk hN cuts ha hρ haT
  let G : ℝ := ((Finset.univ.filter fun j : Fin K =>
    a ≤ columnTime N j ∧ columnTime N j ≤ a+ρ ∧
      GoodColumn (cuts.profile (by omega) j) (goodThreshold k aT)).card : ℝ)
  have hG : aT*ρ/2 ≤ Real.log (k : ℝ)*(G/logScale N) := by
    change _ ≤ (aT/4)*ρ+Real.log (k : ℝ)*(G/logScale N+2/logScale N) at hupper
    have heq : Real.log (k : ℝ)*(G/logScale N+2/logScale N) =
        Real.log (k : ℝ)*(G/logScale N)+2*Real.log (k : ℝ)/logScale N := by ring
    rw [heq] at hupper
    have hh := (abs_le.mp herr').1
    have hsimp : a+ρ-a = ρ := by ring
    rw [hsimp] at hlo
    linarith
  have hG' : (aT*ρ/2)*logScale N ≤ Real.log (k : ℝ)*G := by
    apply (le_div_iff₀ hL).mp
    simpa only [mul_div_assoc] using hG
  change (aT/(4*Real.log (k : ℝ)))*ρ*logScale N ≤ G
  apply (mul_le_mul_iff_right₀ hM).mp
  have heq : Real.log (k : ℝ)*((aT/(4*Real.log (k : ℝ)))*ρ*logScale N) =
      aT*ρ*logScale N/4 := by field_simp [hM.ne'] <;> ring
  rw [heq]
  have hpos : 0 ≤ aT*ρ*logScale N := by positivity
  nlinarith

/-- The second conclusion of the manuscript's weak-profile lemma: one pair
`g, γ` works for every fixed positive window length. -/
theorem weaklyInProbability_localGood {k : ℕ} (hk : 2 ≤ k)
    {μ : TimeLaw k} {T : ℝ} (Q : ∀ N, PMF (Cuts k N (horizonDepth N T)))
    (hT : 0 < T) (hμ : MeasurableProfile μ) (hnd : LocallyNondegenerate μ)
    (hweak : WeaklyInProbability μ T Q) :
    ∃ g γ : ℝ, 0 < g ∧ g < 1/(k : ℝ) ∧ 0 < γ ∧ LocalGoodInProbability T Q g γ := by
  obtain ⟨aT, haT, hlower⟩ := hnd T hT
  have hM : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  obtain ⟨hg, hgk, _⟩ := goodThreshold_spec hk haT
  refine ⟨goodThreshold k aT, aT/(4*Real.log (k : ℝ)), hg, hgk, by positivity, ?_⟩
  intro ρ hρ
  have hconv := uniform_cumulative_convergence Q hT.le hμ hweak continuous_maxCost
    (maxCost_bounds hk) hM.le (show 0 < aT*ρ/16 by positivity)
  apply probability_tendsto_one_mono Q _ _ hconv
  filter_upwards [eventually_ge_atTop
    (transferThreshold (2*Real.log (k : ℝ)) (aT*ρ/2))] with N hlarge
  intro cuts hcuts
  obtain ⟨hN, hc⟩ := hcuts
  refine ⟨hN, ?_⟩
  have hround := (transferThreshold_spec (2*Real.log (k : ℝ))
    (show 0 < aT*ρ/2 by positivity)).2 N hlarge
  apply localGood_of_cumulative hk hN cuts hμ haT hρ hlower (fun t ht => (hc t ht).le)
  linarith

/-- Exact continuous-test convergence supplies both finite empirical inputs. -/
theorem empirical_inputs {k : ℕ} (hk : 2 ≤ k)
    {μ : TimeLaw k} {T : ℝ} (Q : ∀ N, PMF (Cuts k N (horizonDepth N T)))
    (hT : 0 < T) (hμ : MeasurableProfile μ) (hnd : LocallyNondegenerate μ)
    (hweak : WeaklyInProbability μ T Q) :
    IntervalErrorsInProbability μ T Q ∧
      ∃ g γ : ℝ, 0 < g ∧ g < 1/(k : ℝ) ∧ 0 < γ ∧ LocalGoodInProbability T Q g γ :=
  ⟨weaklyInProbability_intervalErrors hk Q hT hμ hweak,
    weaklyInProbability_localGood hk Q hT hμ hnd hweak⟩

end RiffleMain.Profile
