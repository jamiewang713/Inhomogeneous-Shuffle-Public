import RiffleUpperV2.Shared.Empirical

noncomputable section
namespace RiffleUpperV2.Localization

/-- The logarithm always uses the original population N, not the current n. -/
def normalizedExponent (N : ℕ) (μ : ℝ) : ℝ := Real.log μ / Real.log (N : ℝ)

def fluctuation (N : ℕ) (ω : ℝ) : ℝ := normalizedExponent N ω / 2

def crossingPenalty (N : ℕ) (χ : ℝ) : ℝ := Real.log (1 / χ) / Real.log (N : ℝ)

/-- The actual side comparison implies the source's normalized comparison. -/
theorem fluctuationComparison {N : ℕ} (hN : 1 < N) {μ ω χ : ℝ}
    (hμ : 0 < μ) (hχ : 0 < χ) (hcross : χ * μ ≤ ω) :
    normalizedExponent N μ - crossingPenalty N χ ≤ 2 * fluctuation N ω := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hω : 0 < ω := lt_of_lt_of_le (mul_pos hχ hμ) hcross
  have h := Real.log_le_log (mul_pos hχ hμ) hcross
  rw [Real.log_mul hχ.ne' hμ.ne'] at h
  simp only [normalizedExponent, crossingPenalty, fluctuation, one_div, Real.log_inv, neg_div]
  have hh := (div_le_div_iff_of_pos_right hlog).2 h
  rw [add_div] at hh
  linarith

/-- A proper stop was not stopped at the join. -/
theorem properFluctuationLower {V F δ q : ℝ}
    (hcomparison : V - q ≤ 2 * F) (hjoin : δ ≤ V - F) : δ - q ≤ F := by
  linarith

theorem properFluctuationPositive {V F δ q : ℝ}
    (hcomparison : V - q ≤ 2 * F) (hjoin : δ ≤ V - F) (hq : q ≤ δ/2) :
    δ/2 ≤ F := by
  have := properFluctuationLower hcomparison hjoin
  linarith

/-- This estimate does not require the join to have failed its stopping test. -/
theorem terminalStoppingBound {V F ℓ η q : ℝ}
    (hcomparison : V - q ≤ 2 * F) (hdesc : ℓ ≤ V) (hterminal : ℓ ≤ -η) :
    ℓ - F ≤ (q - η) / 2 := by
  linarith

theorem terminalStops {V F ℓ η q δ : ℝ}
    (hcomparison : V - q ≤ 2 * F) (hdesc : ℓ ≤ V) (hterminal : ℓ ≤ -η)
    (hscale : (q - η) / 2 < δ) : ℓ - F < δ := by
  exact lt_of_le_of_lt (terminalStoppingBound hcomparison hdesc hterminal) hscale

/-- Large immediate-stop joins also have strictly positive fluctuation. -/
theorem largeStableFluctuation {ℓ F δ : ℝ} (hlarge : 2 * δ ≤ ℓ)
    (hstable : ℓ - F < δ) : δ < F := by
  linarith

/-- The mean length of a proper parent exceeds twice the endpoint halfwidth. -/
theorem parentMean_gt_two_windows {N : ℕ} (hN : 1 < N) {μ F δ : ℝ}
    (hparent : (N : ℝ) ^ (F + δ) ≤ μ) (hgap : 2 < (N : ℝ) ^ (3*δ/4)) :
    2 * (N : ℝ) ^ (F + δ/4) < μ := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hN)
  have hw : 0 < (N : ℝ) ^ (F + δ/4) := Real.rpow_pos_of_pos hpos _
  have hdecomp : (N : ℝ) ^ (F + δ) =
      (N : ℝ) ^ (3*δ/4) * (N : ℝ) ^ (F + δ/4) := by
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  rw [hdecomp] at hparent
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hgap hw) hparent

end RiffleUpperV2.Localization
