import RiffleLowerV2.ProfileTransfer.Spatial
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open Set
open scoped BigOperators NNReal
namespace RiffleUpperV2.Margins
open TimeProfile

/-- The logarithm is uniformly Lipschitz above a positive lower bound. -/
theorem abs_log_sub_le {b x y : ℝ} (hb : 0 < b) (hx : b ≤ x) (hy : b ≤ y) :
    |Real.log x - Real.log y| ≤ |x-y| / b := by
  have hxp := hb.trans_le hx
  have hyp := hb.trans_le hy
  have hdir : ∀ x y : ℝ, b ≤ x → b ≤ y → y ≤ x →
      Real.log x - Real.log y ≤ (x-y)/b := by
    intro x y hx hy hyx
    have hxp := hb.trans_le hx
    have hyp := hb.trans_le hy
    have hl := Real.log_le_sub_one_of_pos (div_pos hxp hyp)
    rw [Real.log_div hxp.ne' hyp.ne'] at hl
    calc
      Real.log x - Real.log y ≤ (x-y)/y := by convert hl using 1 <;> field_simp
      _ ≤ (x-y)/b := div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hb hy
  rcases le_total y x with hyx | hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hyp hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hdir x y hx hy hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hxp hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [neg_sub] using hdir y x hy hx hxy

/-- The closed simplex permits zero coordinates in this derivative estimate. -/
theorem abs_rpow_sub_le_four {x y θ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (hθ : θ ∈ Icc (2 : ℝ) 4) :
    |x^θ-y^θ| ≤ 4*|x-y| := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => t^θ) (θ*t^(θ-1)) (Icc (0 : ℝ) 1) t := by
    intro t _
    exact (Real.hasDerivAt_rpow_const (Or.inr (by linarith [hθ.1]))).hasDerivWithinAt
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖θ*t^(θ-1)‖ ≤ (4 : ℝ) := by
    intro t ht
    have hp0 := Real.rpow_nonneg ht.1 (θ-1)
    have hp1 := Real.rpow_le_one ht.1 ht.2 (by linarith [hθ.1] : 0 ≤ θ-1)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hθ.1]) hp0)]
    nlinarith [hθ.1, hθ.2]
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hy hx

theorem pileMax_le_of_prob_le {k : ℕ} (p : Simplex k) {b : ℝ}
    (hb : 0 ≤ b) (hp : ∀ l, prob p l ≤ b) : pileMax p ≤ b := by
  unfold pileMax
  exact_mod_cast (Finset.sup_le (s := Finset.univ)
    (f := fun l : Fin k => (⟨prob p l, prob_nonneg p l⟩ : ℝ≥0))
    (a := (⟨b, hb⟩ : ℝ≥0)) (fun l _ => hp l))

theorem pileMax_stability {k : ℕ} (p q : Simplex k) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (hpq : ∀ l, |prob p l - prob q l| ≤ ζ) :
    |pileMax p - pileMax q| ≤ ζ := by
  apply abs_le.mpr
  have hp := pileMax_le_of_prob_le p (add_nonneg (pileMax_nonneg q) hζ)
    (fun l => by linarith [(abs_le.mp (hpq l)).2, prob_le_pileMax q l])
  have hq := pileMax_le_of_prob_le q (add_nonneg (pileMax_nonneg p) hζ)
    (fun l => by linarith [(abs_le.mp (hpq l)).1, prob_le_pileMax p l])
  constructor <;> linarith

theorem maxCost_stability {k : ℕ} (hk : 2 ≤ k) (p q : Simplex k)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hpq : ∀ l, |prob p l - prob q l| ≤ ζ) :
    |maxCost p - maxCost q| ≤ (k : ℝ)*ζ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hh := abs_log_sub_le (one_div_pos.mpr hkpos)
    (inv_card_le_pileMax (by omega) p) (inv_card_le_pileMax (by omega) q)
  simp only [maxCost, digitCost, one_div, Real.log_inv, neg_sub_neg, abs_sub_comm] at hh ⊢
  calc
    _ ≤ |pileMax p-pileMax q| / (1/(k : ℝ)) := by simpa only [abs_sub_comm, one_div] using hh
    _ ≤ ζ / (1/(k : ℝ)) := div_le_div_of_nonneg_right (pileMax_stability p q hζ hpq)
      (one_div_nonneg.mpr hkpos.le)
    _ = (k : ℝ)*ζ := by field_simp

/-- Jensen's fourth-power estimate supplies k^(-3), including boundary vectors. -/
theorem powerSum_lower {k : ℕ} (hk : 2 ≤ k) (p : Simplex k)
    {θ : ℝ} (hθ : θ ∈ Icc (2 : ℝ) 4) :
    1/(k : ℝ)^3 ≤ powerSum p θ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkne := hkpos.ne'
  have hmean := Real.pow_arith_mean_le_arith_mean_pow Finset.univ
    (fun _ : Fin k => 1/(k : ℝ)) (fun l => prob p l)
    (fun _ _ => by positivity)
    (by simp [hkne]) (fun l _ => prob_nonneg p l) 4
  simp only [← Finset.mul_sum, sum_prob, mul_one] at hmean
  have hpow : 1/(k : ℝ)^3 ≤ ∑ l, (prob p l)^4 := by
    have hh := mul_le_mul_of_nonneg_left hmean hkpos.le
    field_simp at hh ⊢
    nlinarith [sq_nonneg ((k : ℝ)^2)]
  apply hpow.trans
  apply Finset.sum_le_sum
  intro l _
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge' (prob_nonneg p l) (prob_le_one p l) (by linarith [hθ.1]) hθ.2

theorem psi_stability {k : ℕ} (hk : 2 ≤ k) (p q : Simplex k)
    {θ ζ : ℝ} (hθ : θ ∈ Icc (2 : ℝ) 4) (_hζ : 0 ≤ ζ)
    (hpq : ∀ l, |prob p l - prob q l| ≤ ζ) :
    |psi p θ - psi q θ| ≤ 4*(k : ℝ)^4*ζ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsum : |powerSum p θ - powerSum q θ| ≤ 4*(k : ℝ)*ζ := by
    unfold powerSum
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ l, |prob p l^θ-prob q l^θ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin k, 4*ζ := Finset.sum_le_sum fun l _ =>
        (abs_rpow_sub_le_four ⟨prob_nonneg p l, prob_le_one p l⟩
          ⟨prob_nonneg q l, prob_le_one q l⟩ hθ).trans
            (mul_le_mul_of_nonneg_left (hpq l) (by norm_num))
      _ = 4*(k : ℝ)*ζ := by simp; ring
  have hh := abs_log_sub_le (show 0 < 1/(k : ℝ)^3 by positivity)
    (powerSum_lower hk p hθ) (powerSum_lower hk q hθ)
  simp only [psi, neg_sub_neg, abs_sub_comm] at hh ⊢
  calc
    _ ≤ |powerSum p θ-powerSum q θ| / (1/(k : ℝ)^3) := by
      simpa only [abs_sub_comm, one_div] using hh
    _ ≤ (4*(k : ℝ)*ζ) / (1/(k : ℝ)^3) :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ = 4*(k : ℝ)^4*ζ := by field_simp

end RiffleUpperV2.Margins
