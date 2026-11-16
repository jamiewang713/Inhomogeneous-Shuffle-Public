import RiffleProfiles.AsymptoticFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter Topology
namespace RiffleUpperV2.Compat

theorem fixed_polynomial_le_rpow (c T : ℝ) (m : ℕ) (η : ℝ)
    (hc : 0 ≤ c) (hT : 0 ≤ T) (hη : 0 < η) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N K : ℕ, N0 ≤ N →
      (K : ℝ) ≤ T * TimeProfile.logScale N →
      c * ((K + 1 : ℕ) : ℝ) ^ m ≤ (N : ℝ) ^ η := by
  have hpoly : (fun x : ℝ => c * (T + 1) ^ m * (Real.log x) ^ m) =o[atTop]
      (fun x : ℝ => x ^ η) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (m : ℝ) hη).const_mul_left (c * (T + 1) ^ m)
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have he := hcast.eventually (hpoly.bound (by norm_num : (0 : ℝ) < 1))
  have hlog := (Real.tendsto_log_atTop.comp hcast).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (he.and hlog)
  refine ⟨max 2 N0, le_max_left _ _, ?_⟩
  intro N K hN hK
  obtain ⟨hbound, hL⟩ := hN0 N ((le_max_right _ _).trans hN)
  change 1 ≤ Real.log (N : ℝ) at hL
  have hL0 : 0 ≤ TimeProfile.logScale N := zero_le_one.trans hL
  have hK1 : ((K + 1 : ℕ) : ℝ) ≤ (T + 1) * TimeProfile.logScale N := by
    push_cast
    dsimp [TimeProfile.logScale] at hK ⊢
    nlinarith
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (K + 1) : (0 : ℝ) ≤ (K + 1 : ℕ)) hK1 m
  have hmajor : c * ((K + 1 : ℕ) : ℝ) ^ m ≤
      c * (T + 1) ^ m * TimeProfile.logScale N ^ m := by
    calc
      _ ≤ c * ((T + 1) * TimeProfile.logScale N) ^ m :=
        mul_le_mul_of_nonneg_left hp hc
      _ = _ := by rw [mul_pow]; ring
  have hnonneg : 0 ≤ c * (T + 1) ^ m * (Real.log (N : ℝ)) ^ m := by
    exact mul_nonneg (mul_nonneg hc (pow_nonneg (by linarith) _))
      (pow_nonneg hL0 _)
  rw [Real.norm_of_nonneg hnonneg,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) η), one_mul] at hbound
  exact hmajor.trans hbound

end RiffleUpperV2.Compat
