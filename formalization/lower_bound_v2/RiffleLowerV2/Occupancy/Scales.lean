import RiffleLowerV2.Factorial.Main

noncomputable section
open scoped Topology
open Filter

namespace RiffleLowerV2.Occupancy
open TimeProfile

def tau (N : ℕ) : ℝ := (N : ℝ)^(-1/100 : ℝ)
def centralBound (N : ℕ) : ℝ := logScale N / 10
def momentRadius (N : ℕ) : ℕ := ⌊(N : ℝ)^(1/25 : ℝ)⌋₊
def bonferroniOrder (N : ℕ) : ℕ := 2 * (momentRadius N / 4)
def momentError (D C : ℝ) (N : ℕ) : ℝ :=
  D * (C * logScale N + 1) * (momentRadius N : ℝ)^2 / N

theorem bonferroniOrder_even (N : ℕ) : Even (bonferroniOrder N) := by
  exact ⟨momentRadius N / 4, by simp [bonferroniOrder]; ring⟩

theorem two_mul_bonferroniOrder_le (N : ℕ) :
    2 * bonferroniOrder N ≤ momentRadius N := by
  have := Nat.div_mul_le_self (momentRadius N) 4
  dsimp [bonferroniOrder]
  omega

theorem momentRadius_le {N : ℕ} (hN : 1 ≤ N) :
    (momentRadius N : ℝ) ≤ (N : ℝ)^(1/5 : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (Nat.floor_le (Real.rpow_nonneg (by positivity) _)).trans
    (Real.rpow_le_rpow_of_exponent_le hNr (by norm_num))

theorem order_bounds {N : ℕ} (hx : 10 ≤ (N : ℝ)^(1/25 : ℝ)) :
    2 ≤ bonferroniOrder N ∧ (N : ℝ)^(1/25 : ℝ)/4 ≤ bonferroniOrder N ∧
      (bonferroniOrder N : ℝ) ≤ (N : ℝ)^(1/25 : ℝ) := by
  have hR : 10 ≤ momentRadius N := Nat.le_floor hx
  have hdiv : momentRadius N < 4 * (momentRadius N / 4) + 4 := by omega
  have hfloor := Nat.lt_floor_add_one ((N : ℝ)^(1/25 : ℝ))
  have hdivr : (momentRadius N : ℝ) < 4 * (momentRadius N / 4 : ℕ) + 4 := by
    exact_mod_cast hdiv
  have hfloor' : (N : ℝ)^(1/25 : ℝ) < (momentRadius N : ℝ) + 1 := hfloor
  have hlow : (N : ℝ)^(1/25 : ℝ)/4 ≤ (bonferroniOrder N : ℝ) := by
    dsimp [bonferroniOrder]
    push_cast
    nlinarith
  refine ⟨by dsimp [bonferroniOrder]; omega, hlow, ?_⟩
  have hmR : bonferroniOrder N ≤ momentRadius N := by
    have := two_mul_bonferroniOrder_le N
    omega
  have hmR' : (bonferroniOrder N : ℝ) ≤ momentRadius N := by exact_mod_cast hmR
  exact hmR'.trans (Nat.floor_le (Real.rpow_nonneg (by positivity) _))

theorem momentError_nonneg {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    {N : ℕ} (hN : 1 ≤ N) : 0 ≤ momentError D C N := by
  have hlog : 0 ≤ logScale N := Real.log_nonneg (by exact_mod_cast hN)
  unfold momentError
  positivity

theorem coarseMomentError_tendsto (D C : ℝ) (hD : 0 < D) :
    Tendsto (fun N : ℕ => D*(C*logScale N+1)*((N : ℝ)^(1/5 : ℝ))^2/N)
      atTop (𝓝 0) := by
  have h := Factorial.momentBudget_tendsto (2/D) C
  have hcoef : 2 / (2 / D) = D := by field_simp
  simpa only [hcoef] using h

/-- All thresholds precede the words, means, and moment orders. -/
theorem eventual_central_scales (D C : ℝ) (hD : 0 < D) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      2 ≤ N ∧ 1 ≤ logScale N ∧ 2 ≤ bonferroniOrder N ∧
      Even (bonferroniOrder N) ∧ 2*bonferroniOrder N ≤ momentRadius N ∧
      (momentRadius N : ℝ) ≤ (N : ℝ)^(1/5 : ℝ) ∧
      (N : ℝ)^(1/25 : ℝ)/4 ≤ (bonferroniOrder N : ℝ) ∧
      (bonferroniOrder N : ℝ) ≤ N ∧
      3*logScale N ≤ (bonferroniOrder N : ℝ)*Real.log 2 ∧
      (logScale N)^3 ≤ (N : ℝ)^(1/50 : ℝ) ∧
      0 ≤ momentError D C N ∧ momentError D C N ≤ 1 := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  have hx := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/25)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (10 : ℝ))
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlr := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/25)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).eventually
      (eventually_lt_nhds (show (0 : ℝ) < Real.log 2 / 12 by positivity))
  have hcube := ((isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0 : ℝ) < 1/50)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have heps := (coarseMomentError_tendsto D C hD).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hall : ∀ᶠ N : ℕ in atTop, _ :=
    (eventually_ge_atTop 2).and (hlog.and (hx.and (hlr.and (hcube.and heps))))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hall
  refine ⟨N0, ?_⟩
  intro N hN
  obtain ⟨hN2, hL, hxN, hlrN, hcubeN, hepsN⟩ := hN0 N hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hxpos : 0 < (N : ℝ)^(1/25 : ℝ) := Real.rpow_pos_of_pos hNr _
  obtain ⟨hm2, hmlow, hmhigh⟩ := order_bounds hxN
  have hpowN : (N : ℝ)^(1/25 : ℝ) ≤ N := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
      (show (1/25 : ℝ) ≤ 1 by norm_num)
  have hlogmul : 3*logScale N ≤ (bonferroniOrder N : ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ hxpos).mp hlrN
    have hh' := mul_le_mul_of_nonneg_right hmlow htwo.le
    dsimp [logScale] at *
    nlinarith
  have hcube' : (logScale N)^3 ≤ (N : ℝ)^(1/50 : ℝ) := by
    have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hNr (1/50 : ℝ))).mp hcubeN
    norm_num only [Real.rpow_ofNat, one_mul] at hh
    exact hh.le
  refine ⟨hN2, hL, hm2, bonferroniOrder_even N, two_mul_bonferroniOrder_le N,
    momentRadius_le hN1, hmlow, hmhigh.trans hpowN, hlogmul, hcube',
    momentError_nonneg hD.le hC.le hN1, ?_⟩
  apply le_trans ?_ hepsN.le
  unfold momentError
  gcongr
  exact momentRadius_le hN1

end RiffleLowerV2.Occupancy
