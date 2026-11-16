import RiffleUpperV2.Margins.FixedPartition
import RiffleUpperV2.Margins.Suffix
import RiffleLowerV2.ProfileTransfer.Margin
import RiffleUpperV2.Shared.Infimum

noncomputable section
open Set MeasureTheory
namespace RiffleUpperV2.Margins
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer RiffleLowerV2.Targets

theorem expression_grid_adapter {k N K : ℕ} (hN : 2 ≤ N) (cuts : Cuts k N K)
    (θ : ℝ) {s u : ℕ} (hsu : s ≤ u) (huK : u ≤ K) :
    empiricalExpression N 0 cuts (deckPos hN) θ s u =
      F cuts (deckPos hN) θ (gridTime N s) (gridTime N u) := by
  have hNlog : Real.log (N : ℝ) ≠ 0 := (logScale_pos hN).ne'
  unfold empiricalExpression empiricalBeta F beta
  rw [empiricalA_grid_adapter hN 0 cuts (deckPos hN) (Nat.zero_le s),
    empiricalB_grid_adapter hN 0 cuts (deckPos hN) θ hsu,
    empiricalB_grid_adapter hN 0 cuts (deckPos hN) 2 (by omega : u ≤ 0+K)]
  simp [A, B, horizon, gridTime, hNlog]

theorem lowerF_continuousOn_theta {k N K : ℕ} (cuts : Cuts k N K)
    (hn : 0 < N) (s u : ℝ) :
    ContinuousOn (fun θ => F cuts hn θ s u) (Icc (3 : ℝ) 4) := by
  exact ((((continuousOn_id.add continuousOn_const).div_const 2).mul continuousOn_const).sub
    (continuousOn_empiricalIntegral_param (fun j => psi_continuousOn_theta (cuts.profile hn j)) s u)).sub
      continuousOn_const

/-- The actual integer-pair infimum is bounded by the interpolated variational
supremum; compactness supplies the real-infimum side conditions explicitly. -/
theorem empiricalInf_le_interpolatedLambda {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) {s u : ℕ} (hsu : s ≤ u) (huK : u ≤ K) :
    empiricalInf N 0 cuts (deckPos hN) s u ≤ lambda1 cuts (deckPos hN) := by
  have hbound : BddAbove ((fun su : ℝ × ℝ =>
      sInf ((fun θ => F cuts (deckPos hN) θ su.1 su.2) '' Icc 3 4)) '' triangle (horizon N K)) := by
    refine ⟨3, ?_⟩
    rintro _ ⟨su, hsu, rfl⟩
    have hb := (isCompact_Icc.image_of_continuousOn
      (lowerF_continuousOn_theta cuts (deckPos hN) su.1 su.2)).bddBelow
    have hi := csInf_le hb (show F cuts (deckPos hN) 3 su.1 su.2 ∈
      (fun θ => F cuts (deckPos hN) θ su.1 su.2) '' Icc 3 4 from ⟨3, by norm_num, rfl⟩)
    have hA := empiricalIntegral_nonneg hN
      (fun j => (maxCost_bounds hk (cuts.profile (deckPos hN) j)).1) hsu.1
    have hB := empiricalIntegral_nonneg hN
      (fun j => (psi_bounds hk (cuts.profile (deckPos hN) j) (show (3 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num)).1)
      hsu.2.1
    have hD := empiricalIntegral_nonneg hN
      (fun j => (psi_bounds hk (cuts.profile (deckPos hN) j) (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num)).1)
      hsu.2.2
    exact hi.trans (by dsimp [F, beta, A, B]; linarith)
  have hsuGrid : (gridTime N s, gridTime N u) ∈ triangle (horizon N K) := by
    refine ⟨div_nonneg (Nat.cast_nonneg s) (logScale_pos hN).le, ?_, ?_⟩
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hsu) (logScale_pos hN).le
    · exact div_le_div_of_nonneg_right (by exact_mod_cast huK) (logScale_pos hN).le
  have hi := le_csSup hbound (show
    sInf ((fun θ => F cuts (deckPos hN) θ (gridTime N s) (gridTime N u)) '' Icc 3 4) ∈
      (fun su : ℝ × ℝ => sInf ((fun θ => F cuts (deckPos hN) θ su.1 su.2) '' Icc 3 4)) ''
        triangle (horizon N K) from ⟨(gridTime N s, gridTime N u), hsuGrid, rfl⟩)
  simpa only [empiricalInf, lambda1, expression_grid_adapter hN cuts _ hsu huK] using hi

/-- Transfer to the new upper negative-margin predicate. The explicitly
displayed 14*log k/log N terminal error reuses the verified two-sided scalar
bound; it is weaker than the manuscript's one-sided 2*log k/log N but vanishes
under exactly the same order of parameter choices. -/
theorem profileToEmpiricalMargin {k N : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    {T e η : ℝ} (hT : 0 < T) (he : 0 ≤ e)
    (P : BorelPartition k) (μ : TimeLaw k) (hμ : ScalarIntegrable μ P T)
    (cuts : HorizonCuts k N T)
    (herrors : ProfileIntervalErrors T cuts (deckPos hN) μ e)
    (hterminal : macroBeta μ T ≤ -η) (hvariational : macroLambda1 μ T ≤ -η) :
    EmpiricalNegativeMargin N 0 cuts (deckPos hN)
      (η-(13/2 : ℝ)*e-14*Real.log (k : ℝ)/logScale N) := by
  have h := marginTransfer k N hk hN T hT P μ hμ cuts e he herrors
  have hlog : 0 ≤ Real.log (k : ℝ)/logScale N :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))) (logScale_pos hN).le
  constructor
  · have hgrid : empiricalBeta N 0 cuts (deckPos hN) (0+horizonDepth N T) =
        beta cuts (deckPos hN) (horizon N (horizonDepth N T)) := by
      unfold empiricalBeta beta
      rw [div_self (show Real.log (N : ℝ) ≠ 0 from (logScale_pos hN).ne')]
      rw [empiricalA_grid_adapter hN 0 cuts (deckPos hN) (by omega : 0 ≤ 0+horizonDepth N T)]
      simp only [A, gridTime, horizon, Nat.sub_zero, Nat.zero_add, Nat.cast_zero, zero_div]
    rw [hgrid]
    have hh := (abs_le.mp h.1).2
    ring_nf at hh hlog ⊢
    linarith
  · intro s u _ hsu huK
    have hi := empiricalInf_le_interpolatedLambda hk hN cuts hsu (by simpa using huK)
    have hh := (abs_le.mp h.2).2
    linarith

/-- The weaker finite rounding constant preserves the requested half-margin. -/
theorem profileMarginLoss_budget {η e rounding : ℝ} (hη : 0 ≤ η)
    (he : e ≤ η/100) (hrounding : rounding ≤ η/4) :
    (13/2 : ℝ)*e+rounding ≤ η/2 := by linarith

/-- An explicit threshold, uniform in profiles, partitions, arrays, and endpoints. -/
theorem profileMarginThreshold (k : ℕ) {η : ℝ} (hη : 0 < η) :
    2 ≤ transferThreshold (14*Real.log (k : ℝ)) η ∧
      ∀ N : ℕ, transferThreshold (14*Real.log (k : ℝ)) η ≤ N →
        14*Real.log (k : ℝ)/logScale N ≤ η/4 :=
  transferThreshold_spec (14*Real.log (k : ℝ)) hη

theorem profileToEmpiricalMargin_half {k N : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hlarge : transferThreshold (14*Real.log (k : ℝ)) η ≤ N)
    (P : BorelPartition k) (μ : TimeLaw k) (hμ : ScalarIntegrable μ P T)
    (cuts : HorizonCuts k N T)
    (herrors : ProfileIntervalErrors T cuts (deckPos hN) μ (η/100))
    (hterminal : macroBeta μ T ≤ -η) (hvariational : macroLambda1 μ T ≤ -η) :
    EmpiricalNegativeMargin N 0 cuts (deckPos hN) (η/2) := by
  have hround := (profileMarginThreshold k hη).2 N hlarge
  have hbudget := profileMarginLoss_budget hη.le (le_refl (η/100)) hround
  exact negativeMargin_mono _ _ (by linarith)
    (profileToEmpiricalMargin hk hN hT (by positivity) P μ hμ cuts herrors hterminal hvariational)

end RiffleUpperV2.Margins
