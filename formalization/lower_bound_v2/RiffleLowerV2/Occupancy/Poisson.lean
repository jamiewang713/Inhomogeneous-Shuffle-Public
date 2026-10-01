import RiffleLowerV2.Factorial.PoissonPolynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2.Occupancy

theorem poissonCollision_hasDerivAt (t : ℝ) :
    HasDerivAt poissonCollision (t * Real.exp (-t)) t := by
  convert! ((hasDerivAt_const t (1 : ℝ)).sub
    (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).mul
      ((hasDerivAt_id t).neg.exp))) using 1
  simp
  ring

theorem poissonCollision_continuous : Continuous poissonCollision :=
  continuous_iff_continuousAt.mpr fun t => (poissonCollision_hasDerivAt t).continuousAt

theorem poissonCollision_mono : MonotoneOn poissonCollision (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) poissonCollision_continuous.continuousOn
  · intro t _
    exact (poissonCollision_hasDerivAt t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(poissonCollision_hasDerivAt t).deriv]
    exact mul_nonneg (le_of_lt (by simpa using ht)) (Real.exp_nonneg _)

theorem poissonCollision_lower (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) * t^2 / 2 ≤ poissonCollision t := by
  have h := mul_le_mul_of_nonneg_right (Real.quadratic_le_exp_of_nonneg ht)
    (Real.exp_nonneg (-t))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  dsimp [poissonCollision]
  nlinarith

theorem poissonCollision_pos {t : ℝ} (ht : 0 < t) : 0 < poissonCollision t :=
  (by positivity : 0 < Real.exp (-t) * t^2 / 2).trans_le (poissonCollision_lower t ht.le)

theorem poissonCollision_upper (t : ℝ) (ht : 0 ≤ t) :
    poissonCollision t ≤ t^2 / 2 := by
  have h := (Factorial.poissonPolynomial_sandwich 2 (by omega)
    (by decide) t ht).1
  norm_num [Factorial.poissonPolynomial, Finset.sum_Icc_succ_top] at h
  linarith

theorem poissonCollision_rare (t : ℝ) (ht : 0 ≤ t) :
    t^2 / 2 - t^3 / 2 ≤ poissonCollision t ∧ poissonCollision t ≤ t^2 / 2 := by
  refine ⟨?_, poissonCollision_upper t ht⟩
  have h := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg t) (sq_nonneg t)
  have hl := poissonCollision_lower t ht
  nlinarith

theorem poissonCollision_elasticity {t : ℝ} (ht : 0 < t) :
    0 ≤ t * deriv poissonCollision t / poissonCollision t ∧
    t * deriv poissonCollision t / poissonCollision t ≤ 2 := by
  rw [(poissonCollision_hasDerivAt t).deriv]
  refine ⟨div_nonneg (mul_nonneg ht.le (mul_nonneg ht.le (Real.exp_nonneg _)))
    (poissonCollision_pos ht).le, (div_le_iff₀ (poissonCollision_pos ht)).mpr ?_⟩
  have h := poissonCollision_lower t ht.le
  nlinarith

theorem poissonCollision_lower_min (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-1) / 2 * min (t^2) 1 ≤ poissonCollision t := by
  by_cases h : t ≤ 1
  · have he := Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ -t by linarith)
    have he' := mul_le_mul_of_nonneg_right he (sq_nonneg t)
    have hs : t^2 ≤ 1 := by nlinarith
    rw [min_eq_left hs]
    have hl := poissonCollision_lower t ht
    nlinarith
  · have hm := poissonCollision_mono (show (1 : ℝ) ∈ Ici 0 by norm_num)
      ht (le_of_not_ge h)
    have hl := poissonCollision_lower 1 (by norm_num)
    have hs : 1 ≤ t^2 := by nlinarith
    rw [min_eq_right hs]
    norm_num at hl
    linarith

theorem poissonCollision_div_sq_antitone :
    AntitoneOn (fun t : ℝ => poissonCollision t / t^2) (Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun t : ℝ => poissonCollision t / t^2)
        ((t * Real.exp (-t) * t^2 - poissonCollision t * (2*t)) / (t^2)^2) t := by
    convert! (poissonCollision_hasDerivAt t).div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 ht.ne') using 1
    simp
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact poissonCollision_continuous.continuousOn.div
      (continuous_pow 2).continuousOn (fun t ht => pow_ne_zero 2 ht.ne')
  · intro t ht
    exact (hd t (by simpa using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have hp : 0 < t := by simpa using ht
    rw [(hd t hp).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_left (poissonCollision_lower t hp.le) hp.le
    nlinarith

theorem poissonCollision_scale_compare {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x^2 * poissonCollision y ≤ y^2 * poissonCollision x := by
  have hy : 0 < y := hx.trans_le hxy
  have h := poissonCollision_div_sq_antitone hx hy hxy
  have h' := (div_le_div_iff₀ (sq_pos_of_pos hy) (sq_pos_of_pos hx)).mp h
  nlinarith

/-- Relative mean changes give a relative benchmark change, uniformly near zero. -/
theorem poissonCollision_stability {x y δ : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hclose : |y-x| ≤ δ*x) :
    |poissonCollision y - poissonCollision x| ≤ 3*δ*poissonCollision x := by
  have hf : 0 ≤ poissonCollision x := (poissonCollision_pos hx).le
  have hx2 : 0 < x^2 := sq_pos_of_pos hx
  obtain ⟨hl, hu⟩ := abs_le.mp hclose
  by_cases hxy : x ≤ y
  · have hm := poissonCollision_mono hx.le hy.le hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hm)]
    have hs := poissonCollision_scale_compare hx hxy
    have hyb : y ≤ (1+δ)*x := by nlinarith
    have hysq : y^2 ≤ ((1+δ)*x)^2 :=
      pow_le_pow_left₀ hy.le hyb 2
    have hdsq : (1+δ)^2 ≤ 1+3*δ := by nlinarith
    have hyb2 : y^2 ≤ (1+3*δ)*x^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hdsq (sq_nonneg x)]
    have hys := mul_le_mul_of_nonneg_right hyb2 hf
    apply (mul_le_mul_iff_right₀ hx2).mp
    nlinarith
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hm := poissonCollision_mono hy.le hx.le hyx
    rw [abs_of_nonpos (sub_nonpos.mpr hm)]
    have hs := poissonCollision_scale_compare hy hyx
    have hyb : (1-δ)*x ≤ y := by nlinarith
    have hysq : ((1-δ)*x)^2 ≤ y^2 :=
      pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hδ1) hx.le) hyb 2
    have hyb2 : (1-2*δ)*x^2 ≤ y^2 := by
      nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg x)]
    have hys := mul_le_mul_of_nonneg_right hyb2 hf
    have he := mul_nonneg (mul_nonneg hδ (sq_nonneg x)) hf
    apply (mul_le_mul_iff_right₀ hx2).mp
    nlinarith

end RiffleLowerV2.Occupancy
