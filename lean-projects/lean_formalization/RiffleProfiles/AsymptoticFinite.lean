import RiffleProfiles.Counting
import RiffleTimeProfile.Base

/-! Frozen A01–A02 and the shared, reviewed logarithmic cutoff facts. -/

set_option autoImplicit false

noncomputable section

namespace RiffleProfiles

def chiLog (χ : ℝ) : ℝ := Real.log (1 / χ)

def exceptionalAllowance (χ : ℝ) : ℝ := 1 / Real.sqrt (chiLog χ)

theorem chiLog_pos {χ : ℝ} (hχ : 0 < χ) (hχ1 : χ < 1) : 0 < chiLog χ := by
  apply Real.log_pos
  exact (lt_div_iff₀ hχ).2 (by simpa using hχ1)

theorem exceptionalAllowance_pos {χ : ℝ} (hχ : 0 < χ) (hχ1 : χ < 1) :
    0 < exceptionalAllowance χ :=
  one_div_pos.mpr (Real.sqrt_pos.2 (chiLog_pos hχ hχ1))

theorem exp_neg_chiLog {χ : ℝ} (hχ : 0 < χ) : Real.exp (-chiLog χ) = χ := by
  simp only [chiLog, one_div, Real.log_inv, neg_neg]
  exact Real.exp_log hχ

theorem exists_chiLog_cutoff (cap U : ℝ) (hcap : 0 < cap) :
    ∃ χ0 : ℝ, 0 < χ0 ∧ χ0 < min 1 cap ∧
      ∀ χ : ℝ, 0 < χ → χ < χ0 → max 1 U ≤ chiLog χ := by
  let B : ℝ := max 1 U + 1
  let χ0 : ℝ := min (cap / 2) (Real.exp (-B))
  have hB : 0 < B := by dsimp [B]; have := le_max_left (1 : ℝ) U; linarith
  have hχ0 : 0 < χ0 := lt_min (by positivity) (Real.exp_pos _)
  have hcap0 : χ0 < cap := (min_le_left _ _).trans_lt (by linarith)
  have hone : χ0 < 1 := (min_le_right _ _).trans_lt (by
    simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hB))
  refine ⟨χ0, hχ0, lt_min hone hcap0, ?_⟩
  intro χ hχ hχlt
  have hsmall : χ < Real.exp (-B) := hχlt.trans_le (min_le_right _ _)
  have hlog : Real.log χ < -B := (Real.log_lt_iff_lt_exp hχ).2 hsmall
  simp only [chiLog, one_div, Real.log_inv]
  dsimp [B] at hlog
  linarith

private theorem power_ratio_eq_exp (b z : ℝ) (hb : 0 < b) (hz : 0 < z)
    (K h : ℕ) :
    b ^ K / z ^ h = Real.exp ((K : ℝ) * Real.log b - (h : ℝ) * Real.log z) := by
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hb, Real.exp_log hz]

/-- A01: a finite weighted upper tail in the exact power-of-N form. -/
theorem scaled_tailWeight_le_rpow (N K : ℕ) (T a β z : ℝ)
    (hN : 2 ≤ N) (_hT : 0 ≤ T) (hK : (K : ℝ) ≤ T * TimeProfile.logScale N)
    (ha : 0 ≤ a) (_hβ : 0 ≤ β) (hz : 1 ≤ z) :
    (N : ℝ) * tailWeight K (Nat.floor (β * TimeProfile.logScale N) + 1) a ≤
      (N : ℝ) ^ (1 + T * Real.log (1 + a * z) - β * Real.log z) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hz0 : 0 < z := zero_lt_one.trans_le hz
  have hb1 : (1 : ℝ) ≤ 1 + a * z := le_add_of_nonneg_right (mul_nonneg ha hz0.le)
  have hb0 := zero_lt_one.trans_le hb1
  have hlogb := Real.log_nonneg hb1
  have hlogz := Real.log_nonneg hz
  have hf : β * TimeProfile.logScale N ≤
      ((Nat.floor (β * TimeProfile.logScale N) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_floor_add_one (β * TimeProfile.logScale N)).le
  have hnum := mul_le_mul_of_nonneg_right hK hlogb
  have hden := mul_le_mul_of_nonneg_right hf hlogz
  calc
    _ ≤ (N : ℝ) * ((1 + a * z) ^ K /
        z ^ (Nat.floor (β * TimeProfile.logScale N) + 1)) :=
      mul_le_mul_of_nonneg_left (tailWeight_le K _ ha hz) hN0.le
    _ = Real.exp (TimeProfile.logScale N + (K : ℝ) * Real.log (1 + a * z) -
        ((Nat.floor (β * TimeProfile.logScale N) + 1 : ℕ) : ℝ) * Real.log z) := by
      rw [power_ratio_eq_exp _ _ hb0 hz0]
      rw [show TimeProfile.logScale N + (K : ℝ) * Real.log (1 + a * z) -
          ((Nat.floor (β * TimeProfile.logScale N) + 1 : ℕ) : ℝ) * Real.log z =
          TimeProfile.logScale N + ((K : ℝ) * Real.log (1 + a * z) -
            ((Nat.floor (β * TimeProfile.logScale N) + 1 : ℕ) : ℝ) * Real.log z) by ring]
      rw [Real.exp_add, TimeProfile.logScale, Real.exp_log hN0]
    _ ≤ Real.exp (TimeProfile.logScale N *
        (1 + T * Real.log (1 + a * z) - β * Real.log z)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = _ := (Real.rpow_def_of_pos hN0 _).symm

/-- A02: the finite sparse-pattern count in the exact power-of-N form. -/
theorem lowCount_le_rpow (N K k : ℕ) (T β z : ℝ)
    (hN : 2 ≤ N) (_hT : 0 ≤ T) (hK : (K : ℝ) ≤ T * TimeProfile.logScale N)
    (hβ : 0 ≤ β) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    (lowCount K (Nat.floor (β * TimeProfile.logScale N)) k : ℝ) ≤
      (N : ℝ) ^ (T * Real.log (1 + (k : ℝ) * z) - β * Real.log z) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hL := TimeProfile.logScale_pos hN
  have hb1 : (1 : ℝ) ≤ 1 + (k : ℝ) * z :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hz0.le)
  have hb0 := zero_lt_one.trans_le hb1
  have hlogb := Real.log_nonneg hb1
  have hlogz := Real.log_nonpos hz0.le hz1
  have hf := Nat.floor_le (mul_nonneg hβ hL.le)
  have hnum := mul_le_mul_of_nonneg_right hK hlogb
  have hden := mul_le_mul_of_nonpos_right hf hlogz
  calc
    _ ≤ (1 + (k : ℝ) * z) ^ K / z ^ Nat.floor (β * TimeProfile.logScale N) :=
      lowCount_le K _ k hz0 hz1
    _ = Real.exp ((K : ℝ) * Real.log (1 + (k : ℝ) * z) -
        (Nat.floor (β * TimeProfile.logScale N) : ℝ) * Real.log z) :=
      power_ratio_eq_exp _ _ hb0 hz0 _ _
    _ ≤ Real.exp (TimeProfile.logScale N *
        (T * Real.log (1 + (k : ℝ) * z) - β * Real.log z)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = _ := (Real.rpow_def_of_pos hN0 _).symm

end RiffleProfiles
