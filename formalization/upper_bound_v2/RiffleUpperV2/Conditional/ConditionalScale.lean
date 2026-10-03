import RiffleUpperV2.Exploration.RegularityDecay

noncomputable section
open Filter Topology
namespace RiffleUpperV2.Conditional
open Exploration

/-- Uniform absorption of the actual refinement count and the all-history error.
The threshold precedes N, the count M, and every refinement exponent r<=a/4. -/
theorem conditionalScale (a ξ A cH Ccur Csum K : ℝ)
    (ha : 0 < a) (hξ : 0 < ξ) (hcH : 0 < cH)
    (hCcur : 0 ≤ Ccur) (hCsum : 0 ≤ Csum) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ (N : ℕ), N0 ≤ N → ∀ (M r : ℝ), 0 ≤ M → 0 ≤ r → r ≤ a/4 →
      M ≤ K*Real.log (N : ℝ)*(N : ℝ)^r →
      (Ccur+M*Csum)*(N : ℝ)^(-a)+
        ((N : ℝ)+2*M*(N : ℝ)^2)*Real.sqrt (badBound N ξ A cH) ≤ C*(N : ℝ)^(-a/2) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)^(a/4)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < a/4)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NL,hNL⟩ := eventually_atTop.mp
    (hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  have h1 := power_sqrt_badBound_tendsto_zero hξ hcH A (a/2+1)
  have h2 := (power_sqrt_badBound_tendsto_zero hξ hcH A (a+2)).const_mul (2*K)
  have he : Tendsto (fun N : ℕ => (N : ℝ)^(a/2)*
      ((N : ℝ)+2*K*(N : ℝ)^(a/2+2))*Real.sqrt (badBound N ξ A cH)) atTop (𝓝 0) := by
    have hh := h1.add h2
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [show a+2 = a/2+(a/2+2) by ring, Real.rpow_add hp,
      Real.rpow_add hp, Real.rpow_one]
    ring
  obtain ⟨NE,hNE⟩ := eventually_atTop.mp
    (he.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨Ccur+K*Csum+1,by positivity,max 2 (max NL NE),le_max_left _ _,?_⟩
  intro N hN M r hM hr hrmax hcount
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : Real.log (N : ℝ) ≤ (N : ℝ)^(a/4) := by
    have hh := hNL N ((le_max_left NL NE).trans ((le_max_right _ _).trans hN))
    simpa only [one_mul] using (div_le_iff₀ (Real.rpow_pos_of_pos hNp _)).mp hh
  have hMc : M ≤ K*(N : ℝ)^(a/2) := by
    apply hcount.trans
    calc
      _ ≤ (K*(N : ℝ)^(a/4))*(N : ℝ)^(a/4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hl hK)
          (Real.rpow_le_rpow_of_exponent_le hN1 hrmax) (by positivity) (by positivity)
      _ = _ := by rw [mul_assoc,← Real.rpow_add hNp]; congr 2; ring
  have hmain : (Ccur+M*Csum)*(N : ℝ)^(-a) ≤
      (Ccur+K*Csum)*(N : ℝ)^(-a/2) := by
    have hpow : (N : ℝ)^(-a) ≤ (N : ℝ)^(-a/2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hprod : (K*(N : ℝ)^(a/2)*Csum)*(N : ℝ)^(-a) =
        (K*Csum)*(N : ℝ)^(-a/2) := by
      calc
        _ = (K*Csum)*((N : ℝ)^(a/2)*(N : ℝ)^(-a)) := by ring
        _ = _ := by rw [← Real.rpow_add hNp]; congr 2; ring
    calc
      _ = Ccur*(N : ℝ)^(-a)+(M*Csum)*(N : ℝ)^(-a) := by ring
      _ ≤ Ccur*(N : ℝ)^(-a/2)+(K*(N : ℝ)^(a/2)*Csum)*(N : ℝ)^(-a) :=
        add_le_add (mul_le_mul_of_nonneg_left hpow hCcur)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMc hCsum) (by positivity))
      _ = _ := by rw [hprod]; ring
  have herror : ((N : ℝ)+2*M*(N : ℝ)^2)*Real.sqrt (badBound N ξ A cH) ≤ (N : ℝ)^(-a/2) := by
    have hh := hNE N ((le_max_right NL NE).trans ((le_max_right _ _).trans hN))
    have hm : ((N : ℝ)+2*M*(N : ℝ)^2)*Real.sqrt (badBound N ξ A cH) ≤
        ((N : ℝ)+2*K*(N : ℝ)^(a/2+2))*Real.sqrt (badBound N ξ A cH) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMc (by norm_num : (0 : ℝ) ≤ 2))
        (sq_nonneg (N : ℝ))
      rw [Real.rpow_add hNp,Real.rpow_two]
      nlinarith
    apply hm.trans
    rw [show -a/2 = -(a/2) by ring,Real.rpow_neg hNp.le,← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp (a/2))).mpr
    nlinarith
  calc
    _ ≤ (Ccur+K*Csum)*(N : ℝ)^(-a/2)+(N : ℝ)^(-a/2) := add_le_add hmain herror
    _ = _ := by ring

end RiffleUpperV2.Conditional
