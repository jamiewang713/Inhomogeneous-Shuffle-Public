import RiffleProfiles.AsymptoticFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Ordered-limit tail estimates A03 and A04 from the frozen contract. -/

noncomputable section

open Filter Topology

namespace RiffleUpperV2.Compat
open RiffleProfiles

private theorem exponential_error_cutoff (A δ η : ℝ) (_hA : 0 ≤ A)
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u → A * Real.exp (-δ * u) ≤ η := by
  have ht : Tendsto (fun u : ℝ => δ * u) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hδ).2 tendsto_id
  have he : Tendsto (fun u : ℝ => Real.exp (-δ * u)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hlim : Tendsto (fun u : ℝ => A * Real.exp (-δ * u)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul A
  obtain ⟨U, hU⟩ := eventually_atTop.1 (hlim.eventually_lt_const hη)
  refine ⟨max 1 U, le_max_left _ _, ?_⟩
  intro u hu
  exact (hU u ((le_max_right _ _).trans hu)).le

private theorem exceptional_exponent_cutoff (A C₀ : ℝ) (hA : 0 ≤ A) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      1 + A * Real.exp (-u / 2) - Real.sqrt u / 2 ≤ -C₀ := by
  obtain ⟨U, hU1, hU⟩ := exponential_error_cutoff A (1 / 2) 1 hA (by norm_num)
    (by norm_num)
  refine ⟨max U (2 * max (C₀ + 2) 0) ^ 2, ?_, ?_⟩
  · have hm := le_max_left U (2 * max (C₀ + 2) 0)
    nlinarith [sq_nonneg (max U (2 * max (C₀ + 2) 0) - 1)]
  intro u hu
  have hmU := le_max_left U (2 * max (C₀ + 2) 0)
  have hmC := le_max_right U (2 * max (C₀ + 2) 0)
  have hC0 := le_max_right (C₀ + 2) 0
  have hCC := le_max_left (C₀ + 2) 0
  have hUu : U ≤ u := by nlinarith [sq_nonneg (max U (2 * max (C₀ + 2) 0) - 1)]
  have he : A * Real.exp (-u / 2) ≤ 1 := by
    convert hU u hUu using 1
    congr 2
    ring
  have hs := Real.le_sqrt_of_sq_le hu
  linarith

/-- A03: the boundary tail retains the exact leading exponent `1-C`. -/
theorem boundary_tailWeight_small_chi (k : ℕ) (T C ε : ℝ)
    (hT : 0 ≤ T) (hC : 0 < C) (hε : 0 < ε) :
    ∃ χ0 : ℝ, 0 < χ0 ∧ χ0 < 1 ∧
      ∀ χ : ℝ, 0 < χ → χ < χ0 → ∀ N K : ℕ,
        2 ≤ N → (K : ℝ) ≤ T * TimeProfile.logScale N →
        (N : ℝ) * tailWeight K
          (Nat.floor ((C / chiLog χ) * TimeProfile.logScale N) + 1) ((k : ℝ) * χ) ≤
          (N : ℝ) ^ (1 - C + ε) := by
  let δ : ℝ := min (1 / 2) (ε / (2 * C))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδC : C * δ ≤ ε / 2 := by
    have hd : δ ≤ ε / (2 * C) := min_le_right _ _
    have hd' := (le_div_iff₀ (by positivity : 0 < 2 * C)).1 hd
    nlinarith
  obtain ⟨U, _, hU⟩ := exponential_error_cutoff (T * (k : ℝ)) δ (ε / 2)
    (by positivity) hδ (by positivity)
  obtain ⟨χ0, hχ00, hχ01, hcut⟩ := exists_chiLog_cutoff 1 U (by norm_num)
  have hχ01' : χ0 < 1 := by simpa using hχ01
  refine ⟨χ0, hχ00, hχ01', ?_⟩
  intro χ hχ hχlt N K hN hK
  have hχ1 := hχlt.trans hχ01'
  have hu := chiLog_pos hχ hχ1
  have he := hU (chiLog χ) ((le_max_right _ _).trans (hcut χ hχ hχlt))
  have hz : 1 ≤ Real.exp ((1 - δ) * chiLog χ) :=
    Real.one_le_exp_iff.2 (mul_nonneg (sub_nonneg.2 hδ1.le) hu.le)
  have hmul : χ * Real.exp ((1 - δ) * chiLog χ) =
      Real.exp (-δ * chiLog χ) := by
    calc
      _ = Real.exp (-chiLog χ) * Real.exp ((1 - δ) * chiLog χ) := by
        rw [exp_neg_chiLog hχ]
      _ = Real.exp (-chiLog χ + (1 - δ) * chiLog χ) := (Real.exp_add _ _).symm
      _ = _ := by congr 1; ring
  have hcancel : C / chiLog χ * Real.log (Real.exp ((1 - δ) * chiLog χ)) =
      C * (1 - δ) := by
    rw [Real.log_exp]
    field_simp
  have hx : 0 ≤ (k : ℝ) * Real.exp (-δ * chiLog χ) := by positivity
  have hlog : Real.log (1 + (k : ℝ) * Real.exp (-δ * chiLog χ)) ≤
      (k : ℝ) * Real.exp (-δ * chiLog χ) := by
    have hl := Real.log_le_sub_one_of_pos (by linarith :
      0 < 1 + (k : ℝ) * Real.exp (-δ * chiLog χ))
    linarith
  have hexponent :
      1 + T * Real.log (1 + ((k : ℝ) * χ) * Real.exp ((1 - δ) * chiLog χ)) -
        C / chiLog χ * Real.log (Real.exp ((1 - δ) * chiLog χ)) ≤ 1 - C + ε := by
    rw [mul_assoc (k : ℝ) χ, hmul, hcancel]
    have hl := mul_le_mul_of_nonneg_left hlog hT
    nlinarith
  exact (scaled_tailWeight_le_rpow N K T ((k : ℝ) * χ) (C / chiLog χ)
    (Real.exp ((1 - δ) * chiLog χ)) hN hT hK (by positivity)
    (div_pos hC hu).le hz).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) hexponent)

/-- A04: exceptional tails beat any prescribed real power, including the factor `N`. -/
theorem exceptional_tailWeight_small_chi (k : ℕ) (T C₀ : ℝ) (hT : 0 ≤ T) :
    ∃ χ0 : ℝ, 0 < χ0 ∧ χ0 < 1 ∧
      ∀ χ : ℝ, 0 < χ → χ < χ0 → ∀ N K : ℕ,
        2 ≤ N → (K : ℝ) ≤ T * TimeProfile.logScale N →
        (N : ℝ) * tailWeight K
          (Nat.floor (exceptionalAllowance χ * TimeProfile.logScale N) + 1)
            ((k : ℝ) * (3 * χ)) ≤ (N : ℝ) ^ (-C₀) := by
  obtain ⟨U, _, hU⟩ := exceptional_exponent_cutoff (3 * T * (k : ℝ)) C₀ (by positivity)
  obtain ⟨χ0, hχ00, hχ01, hcut⟩ := exists_chiLog_cutoff 1 U (by norm_num)
  have hχ01' : χ0 < 1 := by simpa using hχ01
  refine ⟨χ0, hχ00, hχ01', ?_⟩
  intro χ hχ hχlt N K hN hK
  have hχ1 := hχlt.trans hχ01'
  have hu := chiLog_pos hχ hχ1
  have hs := Real.sqrt_pos.2 hu
  have he := hU (chiLog χ) ((le_max_right _ _).trans (hcut χ hχ hχlt))
  have hz : 1 ≤ Real.exp (chiLog χ / 2) :=
    Real.one_le_exp_iff.2 (by positivity)
  have hmul : χ * Real.exp (chiLog χ / 2) = Real.exp (-chiLog χ / 2) := by
    calc
      _ = Real.exp (-chiLog χ) * Real.exp (chiLog χ / 2) := by
        rw [exp_neg_chiLog hχ]
      _ = Real.exp (-chiLog χ + chiLog χ / 2) := (Real.exp_add _ _).symm
      _ = _ := by congr 1; ring
  have hcancel : exceptionalAllowance χ * Real.log (Real.exp (chiLog χ / 2)) =
      Real.sqrt (chiLog χ) / 2 := by
    rw [exceptionalAllowance, Real.log_exp]
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    have hsq := Real.sq_sqrt hu.le
    field_simp
    exact hsq.symm
  have hprod : ((k : ℝ) * (3 * χ)) * Real.exp (chiLog χ / 2) =
      3 * (k : ℝ) * Real.exp (-chiLog χ / 2) := by
    calc
      _ = 3 * (k : ℝ) * (χ * Real.exp (chiLog χ / 2)) := by ring
      _ = _ := by rw [hmul]
  have hx : 0 ≤ 3 * (k : ℝ) * Real.exp (-chiLog χ / 2) := by positivity
  have hlog : Real.log (1 + 3 * (k : ℝ) * Real.exp (-chiLog χ / 2)) ≤
      3 * (k : ℝ) * Real.exp (-chiLog χ / 2) := by
    have hl := Real.log_le_sub_one_of_pos (by linarith :
      0 < 1 + 3 * (k : ℝ) * Real.exp (-chiLog χ / 2))
    linarith
  have hexponent :
      1 + T * Real.log (1 + ((k : ℝ) * (3 * χ)) * Real.exp (chiLog χ / 2)) -
        exceptionalAllowance χ * Real.log (Real.exp (chiLog χ / 2)) ≤ -C₀ := by
    rw [hprod, hcancel]
    have hl := mul_le_mul_of_nonneg_left hlog hT
    nlinarith
  exact (scaled_tailWeight_le_rpow N K T ((k : ℝ) * (3 * χ)) (exceptionalAllowance χ)
    (Real.exp (chiLog χ / 2)) hN hT hK (by positivity)
    (exceptionalAllowance_pos hχ hχ1).le hz).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) hexponent)

end RiffleUpperV2.Compat
