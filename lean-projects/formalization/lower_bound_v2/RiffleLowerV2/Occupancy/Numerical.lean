import RiffleLowerV2.Factorial.Main

noncomputable section
open scoped Topology
open Filter
namespace RiffleLowerV2.Occupancy
open TimeProfile

theorem log_affine_mul_rpow_tendsto (a b r : ℝ) (hr : r < 0) :
    Tendsto (fun N : ℕ => (a*logScale N+b)*(N : ℝ)^r) atTop (𝓝 0) := by
  have hl := (isLittleO_log_rpow_atTop (neg_pos.mpr hr)).tendsto_div_nhds_zero
  have hp := tendsto_rpow_neg_atTop (neg_pos.mpr hr)
  have hh : Tendsto (fun x : ℝ => a*(Real.log x / x^(-r)) + b*x^r) atTop (𝓝 0) := by
    convert (hl.const_mul a).add ((by simpa using hp :
      Tendsto (fun x : ℝ => x^r) atTop (𝓝 0)).const_mul b) using 1
    simp
  have heq : (fun x : ℝ => a*(Real.log x / x^(-r)) + b*x^r) =ᶠ[atTop]
      (fun x : ℝ => (a*Real.log x+b)*x^r) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, div_inv_eq_mul]
    ring
  exact (hh.congr' heq).comp tendsto_natCast_atTop_atTop

/-- Every strict power gap absorbs an arbitrary fixed affine logarithmic factor. -/
theorem eventually_log_affine_mul_rpow_le (a b r q : ℝ) (hrq : r < q) :
    ∀ᶠ N : ℕ in atTop, (a*logScale N+b)*(N : ℝ)^r ≤ (N : ℝ)^q := by
  have h := (log_affine_mul_rpow_tendsto a b (r-q) (sub_neg.mpr hrq)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hh := mul_le_mul_of_nonneg_right hN.le (Real.rpow_nonneg hNp.le q)
  have hid : (N : ℝ)^(r-q) * (N : ℝ)^q = (N : ℝ)^r := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  simpa only [mul_assoc, hid, one_mul] using hh

theorem eventually_const_mul_rpow_le (a r q : ℝ) (hrq : r < q) :
    ∀ᶠ N : ℕ in atTop, a*(N : ℝ)^r ≤ (N : ℝ)^q := by
  simpa using eventually_log_affine_mul_rpow_le 0 a r q hrq

theorem eventually_negative_rpow_le {r e : ℝ} (hr : r < 0) (he : 0 < e) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^r ≤ e := by
  have h : Tendsto (fun N : ℕ => (N : ℝ)^r) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hr)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  exact (h.eventually (eventually_lt_nhds he)).mono fun _ hx => hx.le

theorem exp_logScale_mul {N : ℕ} (hN : 0 < N) (a : ℝ) :
    Real.exp (logScale N*a) = (N : ℝ)^a := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hN)]
  rfl

end RiffleLowerV2.Occupancy
