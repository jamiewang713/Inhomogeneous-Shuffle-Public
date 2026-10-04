import RiffleMain.Critical.Decay

set_option autoImplicit false

/-! The extended critical time separates strict positive and negative margins. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RiffleMain.Critical
open TimeProfile RiffleLowerV2 RiffleUpperV2 RiffleUpperV2.ProfileUpper

/-- Time integrability is derived separately from measurable time profiles. -/
def LocallyScalarIntegrable {k : ℕ} (μ : TimeLaw k) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ P : BorelPartition k, RiffleLowerV2.ScalarIntegrable μ P T

/-- The critical-time argument only needs positivity of costs on every nonempty interval. -/
def PositiveIntervalCosts {k : ℕ} (μ : TimeLaw k) : Prop :=
  ∀ S T : ℝ, 0 ≤ S → S < T → 0 < integratedMaxCost μ S T

/-- Literal local nondegeneracy: the lower bound may vary with the horizon and holds a.e. -/
def LocallyNondegenerate {k : ℕ} (μ : TimeLaw k) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ a : ℝ, 0 < a ∧
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), a ≤ profileMaxCost μ t

/-- The elementary infimum argument needs no finite-shuffle upper-bound machinery. -/
theorem earlierNegative {k : ℕ} {μ : TimeLaw k} {T : ℝ}
    (hcrit : criticalTime μ < ENNReal.ofReal T) :
    ∃ S : ℝ, 0 < S ∧ S < T ∧ reducedMargin μ S < 0 := by
  obtain ⟨x, ⟨S, hS, rfl⟩, hST⟩ := sInf_lt_iff.mp hcrit
  exact ⟨S, hS.1, (ENNReal.ofReal_lt_ofReal_iff'.mp hST).1, hS.2⟩

theorem reducedMargin_strictAnti {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) (hpos : PositiveIntervalCosts μ)
    {S T : ℝ} (hS : 0 ≤ S) (hST : S < T) : reducedMargin μ T < reducedMargin μ S := by
  obtain ⟨P, hP⟩ := hI T (hS.trans_lt hST)
  have hd := reducedMargin_decay hk hS hST.le hP
  have ha := hpos S T hS hST
  linarith

theorem criticalTime_le_of_negative {k : ℕ} {μ : TimeLaw k} {T : ℝ}
    (hT : 0 < T) (hm : reducedMargin μ T < 0) :
    criticalTime μ ≤ ENNReal.ofReal T :=
  sInf_le ⟨T, ⟨hT, hm⟩, rfl⟩

/-- A universal positive lower bound, including profiles whose critical time is infinite. -/
theorem criticalTime_lower {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) :
    ENNReal.ofReal (1 / Real.log (k : ℝ)) ≤ criticalTime μ := by
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  apply le_sInf
  rintro x ⟨T, ⟨hT, hm⟩, rfl⟩
  obtain ⟨P, hP⟩ := hI T hT
  have hb : RiffleLowerV2.macroBeta μ T < 0 := (le_max_left _ _).trans_lt hm
  have ha := scalar_bounds hT.le hP.2.1 (RiffleLowerV2.ProfileTransfer.profileMaxCost_bounds hk μ)
    (show (0 : ℝ) ≤ 0 by rfl) hT.le le_rfl
  have haBound := ha.2
  have ht : 1 / Real.log (k : ℝ) ≤ T := by
    apply (div_le_iff₀ hlog).2
    change integratedMaxCost μ 0 T ≤ Real.log (k : ℝ) * (T - 0) at haBound
    dsimp only [RiffleLowerV2.macroBeta] at hb
    nlinarith
  exact ENNReal.ofReal_le_ofReal ht

theorem criticalTime_pos {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) : 0 < criticalTime μ := by
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hp : 0 < ENNReal.ofReal (1 / Real.log (k : ℝ)) :=
    ENNReal.ofReal_pos.mpr (one_div_pos.mpr hlog)
  exact hp.trans_le (criticalTime_lower hk hI)

theorem positive_below_critical {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) (hpos : PositiveIntervalCosts μ)
    {T : ℝ} (hT : 0 < T) (hcrit : ENNReal.ofReal T < criticalTime μ) :
    0 < reducedMargin μ T := by
  by_contra! hnonpos
  obtain ⟨b, hTb, hbC⟩ := exists_between hcrit
  have hbtop : b ≠ ⊤ := ne_top_of_lt hbC
  have hbreal : ENNReal.ofReal b.toReal = b := ENNReal.ofReal_toReal hbtop
  have hTU : T < b.toReal :=
    (ENNReal.ofReal_lt_ofReal_iff'.mp (by simpa only [hbreal] using hTb)).1
  have hU : 0 < b.toReal := hT.trans hTU
  have hm : reducedMargin μ b.toReal < 0 :=
    (reducedMargin_strictAnti hk hI hpos hT.le hTU).trans_le hnonpos
  have hc := criticalTime_le_of_negative hU hm
  rw [hbreal] at hc
  exact (not_le_of_gt hbC) hc

theorem negative_above_critical {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) {T : ℝ}
    (hcrit : criticalTime μ < ENNReal.ofReal T) : reducedMargin μ T < 0 := by
  obtain ⟨S, hS, hST, hm⟩ := earlierNegative hcrit
  obtain ⟨P, hP⟩ := hI T (hS.trans hST)
  exact (marginMonotonicity hk hS.le hST.le hP).trans_lt hm

theorem positive_of_critical_infinite {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) (hpos : PositiveIntervalCosts μ)
    (hcrit : criticalTime μ = ⊤) {T : ℝ} (hT : 0 < T) : 0 < reducedMargin μ T := by
  apply positive_below_critical hk hI hpos hT
  rw [hcrit]
  exact ENNReal.ofReal_lt_top

end RiffleMain.Critical
