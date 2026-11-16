import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import RiffleProfiles.AsymptoticFinite

/-! Frozen A05: the descriptor count with the source order of parameter choices. -/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace RiffleProfiles

def countErrorExponent (k : ℕ) (T C u : ℝ) : ℝ :=
  3 * T * (k : ℝ) / Real.sqrt u + C * Real.log u / u +
    Real.log u / (2 * Real.sqrt u)

private theorem common_z_parameters {u : ℝ} (hu : 1 ≤ u) :
    0 < 1 / Real.sqrt u ∧ 1 / Real.sqrt u ≤ 1 ∧
      Real.log (1 / Real.sqrt u) = -Real.log u / 2 := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hs0 := Real.sqrt_pos.mpr hu0
  have hs1 : 1 ≤ Real.sqrt u := by simpa using Real.sqrt_le_sqrt hu
  refine ⟨one_div_pos.mpr hs0, (div_le_one hs0).2 hs1, ?_⟩
  rw [one_div, Real.log_inv, Real.log_sqrt hu0.le]
  ring

theorem countErrorExponent_tendsto (k : ℕ) (T C : ℝ) (_hT : 0 ≤ T) (_hC : 0 < C) :
    Tendsto (countErrorExponent k T C) atTop (𝓝 0) := by
  have hinv : Tendsto (fun u : ℝ => 1 / Real.sqrt u) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [Real.rpow_neg hu, ← Real.sqrt_eq_rpow, one_div]
  have hlog : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlogsqrt : Tendsto (fun u : ℝ => Real.log u / Real.sqrt u) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  convert ((hinv.const_mul (3 * T * (k : ℝ))).add (hlog.const_mul C)).add
    (hlogsqrt.const_mul (1 / 2)) using 1
  · ext u
    dsimp [countErrorExponent]
    ring
  · simp

theorem exists_countErrorExponent_cutoff (k : ℕ) (T C η : ℝ)
    (hT : 0 ≤ T) (hC : 0 < C) (hη : 0 < η) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u → countErrorExponent k T C u ≤ η := by
  have he : ∀ᶠ u : ℝ in atTop, countErrorExponent k T C u < η :=
    (countErrorExponent_tendsto k T C hT hC).eventually (eventually_lt_nhds hη)
  obtain ⟨U, hU⟩ := eventually_atTop.mp he
  refine ⟨max 1 U, le_max_left _ _, ?_⟩
  intro u hu
  exact (hU u ((le_max_right _ _).trans hu)).le

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

theorem common_z_count_product_le_rpow (N K k : ℕ) (T C u : ℝ)
    (hN : 2 ≤ N) (hT : 0 ≤ T) (hC : 0 < C) (hu : 1 ≤ u)
    (hK : (K : ℝ) ≤ T * TimeProfile.logScale N) :
    (lowCount K (Nat.floor ((C / u) * TimeProfile.logScale N)) k : ℝ) ^ 2 *
      (lowCount K (Nat.floor ((1 / Real.sqrt u) * TimeProfile.logScale N)) k : ℝ) ≤
      (N : ℝ) ^ (3 * T * Real.log (1 + (k : ℝ) / Real.sqrt u) +
        C * Real.log u / u + Real.log u / (2 * Real.sqrt u)) := by
  have hN0 : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  obtain ⟨hz0, hz1, hlogz⟩ := common_z_parameters hu
  have hb := lowCount_le_rpow N K k T (C / u) (1 / Real.sqrt u)
    hN hT hK (div_nonneg hC.le hu0.le) hz0 hz1
  have he := lowCount_le_rpow N K k T (1 / Real.sqrt u) (1 / Real.sqrt u)
    hN hT hK hz0.le hz0 hz1
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg
    (lowCount K (Nat.floor ((C / u) * TimeProfile.logScale N)) k) : (0 : ℝ) ≤ _) hb 2
  calc
    _ ≤ ((N : ℝ) ^ (T * Real.log (1 + (k : ℝ) * (1 / Real.sqrt u)) -
        (C / u) * Real.log (1 / Real.sqrt u))) ^ 2 *
        (N : ℝ) ^ (T * Real.log (1 + (k : ℝ) * (1 / Real.sqrt u)) -
        (1 / Real.sqrt u) * Real.log (1 / Real.sqrt u)) :=
      mul_le_mul hsq he (Nat.cast_nonneg _) (sq_nonneg _)
    _ = _ := by
      rw [pow_two, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      rw [hlogz, show (k : ℝ) * (1 / Real.sqrt u) = (k : ℝ) / Real.sqrt u by ring]
      ring

theorem count_product_le_error_rpow (N K k : ℕ) (T C u : ℝ)
    (hN : 2 ≤ N) (hT : 0 ≤ T) (hC : 0 < C) (hu : 1 ≤ u)
    (hK : (K : ℝ) ≤ T * TimeProfile.logScale N) :
    (lowCount K (Nat.floor ((C / u) * TimeProfile.logScale N)) k : ℝ) ^ 2 *
      (lowCount K (Nat.floor ((1 / Real.sqrt u) * TimeProfile.logScale N)) k : ℝ) ≤
      (N : ℝ) ^ countErrorExponent k T C u := by
  have hx : 0 ≤ (k : ℝ) / Real.sqrt u :=
    div_nonneg (Nat.cast_nonneg k) (Real.sqrt_nonneg _)
  have hlog : Real.log (1 + (k : ℝ) / Real.sqrt u) ≤ (k : ℝ) / Real.sqrt u := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + (k : ℝ) / Real.sqrt u)
    linarith
  have hexp : 3 * T * Real.log (1 + (k : ℝ) / Real.sqrt u) +
      C * Real.log u / u + Real.log u / (2 * Real.sqrt u) ≤ countErrorExponent k T C u := by
    have hm := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 3 * T)
    convert add_le_add_right (add_le_add_right hm (C * Real.log u / u))
      (Real.log u / (2 * Real.sqrt u)) using 1
    dsimp [countErrorExponent]
    ring
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  exact (common_z_count_product_le_rpow N K k T C u hN hT hC hu hK).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 hexp)

/-- A05: the cutoff in `χ` is fixed before the finite good-count dimension `d`. -/
theorem descriptor_count_le_rpow (k : ℕ) (T C ε : ℝ)
    (hk : 2 ≤ k) (hT : 0 ≤ T) (hC : 0 < C) (hε : 0 < ε) :
    ∃ χ0 : ℝ, 0 < χ0 ∧ χ0 < min 1 (1 / (k : ℝ)) ∧
      ∀ χ : ℝ, 0 < χ → χ < χ0 → ∀ d : ℕ,
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N K : ℕ, N0 ≤ N →
        (K : ℝ) ≤ T * TimeProfile.logScale N →
        ((k ^ 2 * (K + 1) ^ (d + 2) *
          (lowCount K (Nat.floor ((C / chiLog χ) * TimeProfile.logScale N)) k) ^ 2 *
          lowCount K (Nat.floor (exceptionalAllowance χ * TimeProfile.logScale N)) k : ℕ) : ℝ) ≤
        (N : ℝ) ^ ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨U, hU1, hU⟩ := exists_countErrorExponent_cutoff k T C (ε / 2) hT hC hε2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨χ0, hχ0, hχcap, hχU⟩ := exists_chiLog_cutoff (1 / (k : ℝ)) U (by positivity)
  refine ⟨χ0, hχ0, hχcap, ?_⟩
  intro χ hχ hχlt d
  obtain ⟨N0, hN02, hN0⟩ := fixed_polynomial_le_rpow ((k : ℝ) ^ 2) T (d + 2)
    (ε / 2) (sq_nonneg _) hT hε2
  refine ⟨N0, hN02, ?_⟩
  intro N K hN hK
  have hN2 : 2 ≤ N := hN02.trans hN
  have hN0real : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have huU : U ≤ chiLog χ := (le_max_right _ _).trans (hχU χ hχ hχlt)
  have hu1 : 1 ≤ chiLog χ := hU1.trans huU
  have hcounts := (count_product_le_error_rpow N K k T C (chiLog χ)
    hN2 hT hC hu1 hK).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (hU _ huU))
  have hpoly := hN0 N K hN hK
  calc
    _ = ((k : ℝ) ^ 2 * ((K + 1 : ℕ) : ℝ) ^ (d + 2)) *
        ((lowCount K (Nat.floor ((C / chiLog χ) * TimeProfile.logScale N)) k : ℝ) ^ 2 *
        (lowCount K (Nat.floor ((1 / Real.sqrt (chiLog χ)) * TimeProfile.logScale N)) k : ℝ)) := by
      simp only [Nat.cast_mul, Nat.cast_pow, exceptionalAllowance]
      ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul hpoly hcounts (by positivity) (Real.rpow_nonneg hN0real.le _)
    _ = (N : ℝ) ^ ε := by rw [← Real.rpow_add hN0real]; congr 1; ring

end RiffleProfiles
