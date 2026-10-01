import Contracts.v1.ModelThinning
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped Topology
open Filter
namespace RiffleLowerV2.Thinning
open TimeProfile

/-- A polynomial envelope makes the prefix count cost independent of the depth. -/
theorem prefixFailure_le_envelope {N k K : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k)
    {T : ℝ} (hT : 0 < T) (hK : (K : ℝ) ≤ T * logScale N) (ε : ℝ) :
    prefixFailure N k K ε ≤
      2 * (T+1) * (N : ℝ)^(1 + T * Real.log k) *
        Real.exp (-(N : ℝ)^ε / 8) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hlog : logScale N ≤ (N : ℝ) := by
    dsimp [logScale]
    linarith [Real.log_le_sub_one_of_pos hNr]
  have hlin : (K : ℝ) + 1 ≤ (T+1) * N := by
    have := mul_le_mul_of_nonneg_left hlog hT.le
    nlinarith
  have hpow : (k : ℝ)^K ≤ (N : ℝ)^(T * Real.log k) := by
    rw [← Real.rpow_natCast]
    calc
      (k : ℝ)^(K : ℝ) ≤ (k : ℝ)^(T * logScale N) :=
        Real.rpow_le_rpow_of_exponent_le hk1 hK
      _ = (N : ℝ)^(T * Real.log k) := by
        rw [Real.rpow_def_of_pos hkr, Real.rpow_def_of_pos hNr]
        congr 1
        dsimp [logScale]
        ring
  unfold prefixFailure
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    2 * ((K : ℝ)+1) * (k : ℝ)^K ≤
        2 * ((T+1) * N) * (N : ℝ)^(T * Real.log k) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by simpa using hlin) (by norm_num)
      · exact hpow
      · positivity
      · positivity
    _ = 2 * (T+1) * (N : ℝ)^(1 + T * Real.log k) := by
      rw [Real.rpow_add hNr, Real.rpow_one]
      ring

/-- Every fixed real power is dominated by the stretched exponential. -/
theorem tendsto_power_mul_stretchedExp (a ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun x : ℝ => x^a * Real.exp (-x^ε / 8)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (a/ε) (1/8) (by norm_num)).comp (tendsto_rpow_atTop hε)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  change (x^ε)^(a/ε) * Real.exp (-(1/8) * x^ε) = _
  rw [← Real.rpow_mul hx.le]
  have hexp : ε * (a/ε) = a := by field_simp [hε.ne']
  rw [hexp]
  congr 2
  ring

/-- Convergence of the common envelope over all logarithmic depths and all cuts. -/
theorem prefixFailureEnvelope_tendsto (k : ℕ) (T ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      2 * (T+1) * (N : ℝ)^(1 + T * Real.log k) *
        Real.exp (-(N : ℝ)^ε / 8)) atTop (𝓝 0) := by
  have h := ((tendsto_power_mul_stretchedExp (1 + T * Real.log k) ε hε).comp
    tendsto_natCast_atTop_atTop).const_mul (2 * (T+1))
  simpa only [mul_zero, mul_assoc, Function.comp_apply] using h

/-- Frozen LB-02 uniform error limit, with the exact quantifier order. -/
theorem prefixFailureUniform : Targets.PrefixFailureUniform := by
  intro k hk T ε δ hT hε hδ
  have he := (prefixFailureEnvelope_tendsto k T ε hε).eventually
    (eventually_lt_nhds hδ)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp he
  refine ⟨max N0 2, ?_⟩
  intro N hN K hK
  exact (prefixFailure_le_envelope (le_trans (le_max_right _ _) hN) hk hT hK ε).trans
    (hN0 N (le_trans (le_max_left _ _) hN)).le

end RiffleLowerV2.Thinning
