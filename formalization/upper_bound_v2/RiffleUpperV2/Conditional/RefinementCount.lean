import RiffleUpperV2.Exploration.Objects

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration

/-- The fixed logarithmic refinement window costs a genuine real power of N. -/
theorem window_power_le {k N : ℕ} {ρ : ℝ} (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hρ : 0 ≤ ρ) :
    (k : ℝ)^(windowLength N ρ) ≤
      (k : ℝ)^2 * (N : ℝ)^(ρ * Real.log (k : ℝ)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hN0 : (0 : ℝ) < N := by positivity
  have hx : 0 ≤ ρ*Real.log (N : ℝ) :=
    mul_nonneg hρ (Real.log_nonneg (by exact_mod_cast hN))
  have hw : (windowLength N ρ : ℝ) ≤ ρ*Real.log (N : ℝ)+2 := by
    have ht := Nat.ceil_lt_add_one hx
    simp only [windowLength, Nat.cast_add, Nat.cast_one]
    linarith
  calc
    _ = (k : ℝ)^((windowLength N ρ : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (k : ℝ)^(ρ*Real.log (N : ℝ)+2) := Real.rpow_le_rpow_of_exponent_le hk1 hw
    _ = _ := by
      rw [Real.rpow_add hk0, Real.rpow_two]
      have he : (k : ℝ)^(ρ*Real.log (N : ℝ)) = (N : ℝ)^(ρ*Real.log (k : ℝ)) := by
        rw [Real.rpow_def_of_pos hk0, Real.rpow_def_of_pos hN0]
        congr 1
        ring
      rw [he, mul_comm]

/-- Source eq:ub-exploration-block-count. Refining each of at most 2kK
cylinders through at most windowLength additional digits costs this exact
uniform real-power bound; it is not treated as subpolynomial. -/
theorem refinementCount {k N K M : ℕ} {ρ T : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N) (hρ : 0 ≤ ρ)
    (hK : (K : ℝ) ≤ T*Real.log (N : ℝ))
    (hM : M ≤ 2*k*K*k^(windowLength N ρ)) :
    (M : ℝ) ≤ (2*(k : ℝ)^3*T) * Real.log (N : ℝ) *
      (N : ℝ)^(ρ*Real.log (k : ℝ)) := by
  have hp := window_power_le hk hN hρ
  have hTL : 0 ≤ T*Real.log (N : ℝ) := (Nat.cast_nonneg K).trans hK
  have hM' : (M : ℝ) ≤ 2*(k : ℝ)*K*(k : ℝ)^(windowLength N ρ) := by
    exact_mod_cast hM
  calc
    (M : ℝ) ≤ 2*(k : ℝ)*K*(k : ℝ)^(windowLength N ρ) := hM'
    _ ≤ 2*(k : ℝ)*(T*Real.log (N : ℝ))*
        ((k : ℝ)^2*(N : ℝ)^(ρ*Real.log (k : ℝ))) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hK (by positivity)) hp
        (by positivity) (by positivity)
    _ = _ := by ring

end RiffleUpperV2.Conditional
