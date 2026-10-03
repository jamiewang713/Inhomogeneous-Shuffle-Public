import RiffleUpperV2.Exploration.UniformRegularity

noncomputable section
open Filter Topology
namespace RiffleUpperV2.Exploration

/-- A positive stretched exponential dominates every fixed real power. -/
theorem stretchedExp_tendsto_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)^s * Real.exp (-c*(n : ℝ)^a)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s/a) c hc).comp
    ((tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply ht.congr'
  filter_upwards with n
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 2
  field_simp

/-- Any fixed polynomial multiple of r_bad tends to zero. -/
theorem power_badBound_tendsto_zero {ξ c : ℝ} (hξ : 0 < ξ) (hc : 0 < c) (A s : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)^s * badBound n ξ A c) atTop (𝓝 0) := by
  have ht := (stretchedExp_tendsto_zero (by linarith : 0 < ξ/3) hc (s+A)).const_mul A
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  rw [Real.rpow_add hn0]
  unfold badBound
  ring

/-- Any fixed polynomial multiple of the specified square-root history threshold tends to zero. -/
theorem power_sqrt_badBound_tendsto_zero {ξ c : ℝ} (hξ : 0 < ξ) (hc : 0 < c) (A s : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)^s * Real.sqrt (badBound n ξ A c)) atTop (𝓝 0) := by
  have ht := (Real.continuous_sqrt.tendsto 0).comp (power_badBound_tendsto_zero hξ hc A (2*s))
  simp only [Real.sqrt_zero] at ht
  apply ht.congr'
  filter_upwards with n
  dsimp only [Function.comp_def]
  rw [Real.sqrt_mul (Real.rpow_nonneg (Nat.cast_nonneg n) (2*s))]
  have hh : Real.sqrt ((n : ℝ)^(2*s)) = (n : ℝ)^s := by
    rw [mul_comm (2:ℝ) s, Real.rpow_mul (Nat.cast_nonneg n), Real.rpow_two,
      Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
  rw [hh]

/-- The sum of concentration and all-history errors is smaller than every fixed inverse power. -/
theorem historyErrors_eventually_le_power {ξ c : ℝ} (hξ : 0 < ξ) (hc : 0 < c)
    (A b : ℝ) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ n : ℕ, N0 ≤ n →
      badBound n ξ A c + 2*n*Real.sqrt (badBound n ξ A c) ≤ (n : ℝ)^(-b) := by
  have h1 := power_badBound_tendsto_zero hξ hc A b
  have h2 := (power_sqrt_badBound_tendsto_zero hξ hc A (b+1)).const_mul 2
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^b *
      (badBound n ξ A c+2*n*Real.sqrt (badBound n ξ A c))) atTop (𝓝 0) := by
    have hh := h1.add h2
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.rpow_add (by exact_mod_cast (show 0<n by omega)), Real.rpow_one]
    ring
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp (ht.eventually_le_const (by norm_num : (0:ℝ)<1))
  refine ⟨max N0 1,le_max_right _ _,?_⟩
  intro n hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hh := hN0 n ((le_max_left _ _).trans hn)
  rw [Real.rpow_neg hn0.le, ← one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hn0 b)).mpr
  simpa only [mul_comm] using hh

/-- In particular the exact source regularity-error expression is o(1). -/
theorem regularityError_tendsto_zero (k : ℕ) {ξ η c : ℝ} (hξ : 0 < ξ)
    (hξη : ξ < η) (hc : 0 < c) (A : ℝ) :
    Tendsto (fun n : ℕ => badBound n ξ A c+2*n*Real.sqrt (badBound n ξ A c)+
      (k : ℝ)/2*(n : ℝ)^(ξ-η)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => badBound n ξ A c) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero,one_mul] using power_badBound_tendsto_zero hξ hc A 0
  have h2 : Tendsto (fun n : ℕ => 2*n*Real.sqrt (badBound n ξ A c)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,mul_zero,mul_assoc] using
      (power_sqrt_badBound_tendsto_zero hξ hc A 1).const_mul 2
  have h3 : Tendsto (fun n : ℕ => (k : ℝ)/2*(n : ℝ)^(ξ-η)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_sub, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by linarith : 0<η-ξ)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul ((k : ℝ)/2)
  simpa only [add_zero] using (h1.add h2).add h3

end RiffleUpperV2.Exploration
