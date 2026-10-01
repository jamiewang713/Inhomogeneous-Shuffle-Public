import RiffleLowerV2.Shared.Geometry

noncomputable section
open scoped Topology
open Filter TimeProfile
namespace RiffleLowerV2.Types

/-- The only vanishing scale in the rounded-type error. -/
def roundingRate (N : ℕ) : ℝ := (Real.log (logScale N) + 1) / logScale N

lemma roundingRate_tendsto : Tendsto roundingRate atTop (𝓝 0) := by
  have hL : Tendsto (fun N : ℕ => logScale N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hb : Tendsto (fun L : ℝ => (1 : ℝ) / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  unfold roundingRate
  simpa only [Function.comp_def, add_div, zero_add] using (ha.add hb).comp hL

/-- An explicit threshold depending on no array, partition or tilt. -/
def typeThreshold : ℕ := ⌈Real.exp 1⌉₊ + 2

lemma typeThreshold_ge_two : 2 ≤ typeThreshold := by dsimp [typeThreshold]; omega

lemma logScale_ge_one {N : ℕ} (hN : typeThreshold ≤ N) : 1 ≤ logScale N := by
  have he : Real.exp 1 ≤ (⌈Real.exp 1⌉₊ : ℝ) := Nat.le_ceil _
  have hn : (⌈Real.exp 1⌉₊ : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show ⌈Real.exp 1⌉₊ ≤ N by dsimp [typeThreshold] at hN; omega)
  simpa only [Real.log_exp, logScale] using Real.log_le_log (Real.exp_pos 1) (he.trans hn)

/-- Explicit finite remainder coefficient; the logarithmic cutoff is a parameter. -/
def roundConstant (k m : ℕ) (T B : ℝ) : ℝ :=
  (k : ℝ)*m*B + 2 + (m : ℝ)*(2*k+1)*(Real.log (T+1)+3) + Real.log (2+T*B)

lemma roundConstant_pos (k m : ℕ) {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B) :
    0 < roundConstant k m T B := by
  have hlogT : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  have hlogB : 0 ≤ Real.log (2+T*B) := Real.log_nonneg (by nlinarith)
  unfold roundConstant
  positivity

lemma finite_remainder_bound (k m : ℕ) {n L T B : ℝ} (hn : 0 ≤ n) (hL : 1 ≤ L)
    (hT : 0 < T) (hB : 0 ≤ B) (hnT : n ≤ T*L) :
    ((k : ℝ)*m*B + 1 + (m : ℝ)*(2*k+1)*(Real.log (n+1)+2) + Real.log (2+n*B)) / L ≤
      roundConstant k m T B * (Real.log L+1) / L := by
  have hLp : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogT : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  have hlogB : 0 ≤ Real.log (2+T*B) := Real.log_nonneg (by nlinarith)
  have h1 : Real.log (n+1) ≤ Real.log (T+1) + Real.log L := by
    have hh : n+1 ≤ (T+1)*L := by nlinarith
    have ht := Real.log_le_log (by linarith : 0 < n+1) hh
    rwa [Real.log_mul (by positivity : T+1 ≠ 0) hLp.ne'] at ht
  have h2 : Real.log (2+n*B) ≤ Real.log (2+T*B) + Real.log L := by
    have hh : 2+n*B ≤ (2+T*B)*L := by nlinarith [mul_le_mul_of_nonneg_right hnT hB]
    have ht := Real.log_le_log (by positivity : 0 < 2+n*B) hh
    rwa [Real.log_mul (by positivity : 2+T*B ≠ 0) hLp.ne'] at ht
  apply div_le_div_of_nonneg_right _ hLp.le
  have hc : 0 ≤ (m : ℝ)*(2*k+1) := by positivity
  have hkm : 0 ≤ (k : ℝ)*m*B := by positivity
  have he := mul_le_mul_of_nonneg_left (by linarith : Real.log (n+1)+2 ≤
    Real.log (T+1)+Real.log L+2) hc
  unfold roundConstant
  nlinarith [mul_nonneg hkm hlogL,
    mul_nonneg (mul_nonneg hc (by linarith : 0 ≤ Real.log (T+1)+2)) hlogL,
    mul_nonneg hlogB hlogL]

end RiffleLowerV2.Types
