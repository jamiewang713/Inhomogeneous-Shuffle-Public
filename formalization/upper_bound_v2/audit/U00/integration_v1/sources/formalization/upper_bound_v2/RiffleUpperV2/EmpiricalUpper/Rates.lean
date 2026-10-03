import RiffleUpperV2.EmpiricalUpper.ExplorationTV
import RiffleUpperV2.Exploration.RegularityDecay

noncomputable section
open Filter Topology
namespace RiffleUpperV2.EmpiricalUpper
open Exploration Exponential

theorem weightedPower_tendsto (c b D : ℝ) (hcb : c < b) :
    Tendsto (fun N : ℕ => (N : ℝ)^c*(D*(N : ℝ)^(-b))) atTop (𝓝 0) := by
  have hh := ((tendsto_rpow_neg_atTop (sub_pos.mpr hcb)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul D
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  dsimp only [Function.comp_def]
  rw [mul_left_comm, ← Real.rpow_add hNp]
  congr 2
  ring

theorem weightedHistoryErrors_tendsto {ξ cH : ℝ} (hξ : 0 < ξ) (hcH : 0 < cH)
    (A c : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)^c*
      (badBound N ξ A cH+2*N*Real.sqrt (badBound N ξ A cH))) atTop (𝓝 0) := by
  have h1 := power_badBound_tendsto_zero hξ hcH A c
  have h2 := (power_sqrt_badBound_tendsto_zero hξ hcH A (c+1)).const_mul 2
  have ht := h1.add h2
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.rpow_add hNp, Real.rpow_one]
  ring

theorem sqrt_power (N : ℕ) {D : ℝ} (hD : 0 ≤ D) (b : ℝ) :
    Real.sqrt (D*(N : ℝ)^(-b)) = Real.sqrt D*(N : ℝ)^(-b/2) := by
  rw [Real.sqrt_mul hD]
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 2
  ring

/-- A fixed polynomial conditional rate and the concrete regularity errors give
one uniform power bound. No array or horizon enters the choice of c or N0. -/
theorem criterion_polynomial (k B : ℕ) (ξ η A cH C ζ : ℝ)
    (hξ : 0 < ξ) (hξη : ξ < η) (hcH : 0 < cH) (hC : 0 < C) (hζ : 0 < ζ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ((componentConstant B)^(2*k)-1)*(C*(N : ℝ)^(-ζ)) ≤ 1/2 ∧
      Real.sqrt (2*((componentConstant B)^(2*k)-1)*(C*(N : ℝ)^(-ζ)))/2 +
        (badBound N ξ A cH+2*N*Real.sqrt (badBound N ξ A cH)+
          (k : ℝ)/2*(N : ℝ)^(ξ-η)) + (N : ℝ)^(-(1 : ℝ))/(B+1).factorial ≤
          (N : ℝ)^(-c) := by
  let q : ℝ := (componentConstant B)^(2*k)-1
  have hq : 0 ≤ q := by
    have hh := one_le_pow₀ (componentConstant_ge_one B) (n := 2*k)
    dsimp [q]
    linarith
  let c : ℝ := min (ζ/4) (min ((η-ξ)/2) (1/2))
  have hcp : 0 < c := lt_min (by positivity) (lt_min (by linarith) (by norm_num))
  have hcz : c < ζ/2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hce : c < η-ξ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hc1 : c < 1 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  have hsqrt : Tendsto (fun N : ℕ => (N : ℝ)^c*
      (Real.sqrt (2*q*(C*(N : ℝ)^(-ζ)))/2)) atTop (𝓝 0) := by
    have hh := weightedPower_tendsto c (ζ/2) (Real.sqrt (2*q*C)/2) hcz
    apply hh.congr'
    filter_upwards with N
    rw [show 2*q*(C*(N : ℝ)^(-ζ)) = (2*q*C)*(N : ℝ)^(-ζ) by ring,
      sqrt_power N (by positivity)]
    ring
  have hhist := weightedHistoryErrors_tendsto hξ hcH A c
  have hpile : Tendsto (fun N : ℕ => (N : ℝ)^c*((k : ℝ)/2*(N : ℝ)^(ξ-η))) atTop (𝓝 0) := by
    simpa only [neg_sub] using weightedPower_tendsto c (η-ξ) ((k : ℝ)/2) hce
  have htail : Tendsto (fun N : ℕ => (N : ℝ)^c*((N : ℝ)^(-(1 : ℝ))/(B+1).factorial)) atTop (𝓝 0) := by
    simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one] using
      weightedPower_tendsto c 1 (1/((B+1).factorial : ℝ)) hc1
  let f : ℕ → ℝ := fun N =>
    Real.sqrt (2*q*(C*(N : ℝ)^(-ζ)))/2 +
      (badBound N ξ A cH+2*N*Real.sqrt (badBound N ξ A cH)+
        (k : ℝ)/2*(N : ℝ)^(ξ-η)) + (N : ℝ)^(-(1 : ℝ))/(B+1).factorial
  have hnorm : Tendsto (fun N : ℕ => (N : ℝ)^c*f N) atTop (𝓝 0) := by
    have hh := ((hsqrt.add hhist).add hpile).add htail
    simp only [add_zero] at hh
    convert hh using 1
    funext N
    dsimp [f]
    ring
  have hgeom : Tendsto (fun N : ℕ => q*(C*(N : ℝ)^(-ζ))) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc, Function.comp_def] using
      ((tendsto_rpow_neg_atTop hζ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (q*C)
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp (hnorm.eventually_le_const (by norm_num : (0 : ℝ)<1))
  obtain ⟨N2,hN2⟩ := eventually_atTop.mp (hgeom.eventually_le_const (by norm_num : (0 : ℝ)<1/2))
  refine ⟨c,hcp,max 2 (max N1 N2),le_max_left _ _,?_⟩
  intro N hN
  have hN' : 2 ≤ N := (le_max_left _ _).trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hN2 N ((le_max_right N1 N2).trans ((le_max_right _ _).trans hN)),?_⟩
  change f N ≤ (N : ℝ)^(-c)
  rw [Real.rpow_neg hNp.le, ← one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp c)).mpr
  simpa only [mul_comm] using
    hN1 N ((le_max_left N1 N2).trans ((le_max_right _ _).trans hN))

end RiffleUpperV2.EmpiricalUpper
