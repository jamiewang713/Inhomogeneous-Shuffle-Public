import RiffleLowerV2.Thinning.PMFTools
import Mathlib.Analysis.Complex.Exponential

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Thinning

variable {Ω : Type*} [Fintype Ω]

theorem chernoffConstant_pos : 0 < chernoffConstant := by
  unfold chernoffConstant
  have h : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  linarith

/-- The analytic step needs only the stated Poisson transform; concrete models
supply that transform separately. -/
theorem centered_exp_of_transform (P : PMF Ω) (X : Ω → ℕ) (μ : ℝ) (hμ : 0 ≤ μ)
    (htr : ∀ s : ℝ, 0 < s → expect P (fun ω => s ^ X ω) ≤ Real.exp (μ * (s-1)))
    {z : ℝ} (hz : |z| ≤ 1) :
    expect P (fun ω => Real.exp (z * ((X ω : ℝ) - μ))) ≤ Real.exp (μ * z^2) := by
  have hrem : Real.exp z - 1 - z ≤ z^2 :=
    le_trans (le_abs_self _) (Real.abs_exp_sub_one_sub_id_le hz)
  have he : expect P (fun ω => Real.exp (z * (X ω : ℝ))) ≤
      Real.exp (μ * (Real.exp z - 1)) := by
    simpa only [mul_comm z, Real.exp_nat_mul] using htr (Real.exp z) (Real.exp_pos z)
  calc
    _ = Real.exp (-z*μ) * expect P (fun ω => Real.exp (z * (X ω : ℝ))) := by
      rw [← expect_const_mul]
      congr 1
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-z*μ) * Real.exp (μ * (Real.exp z - 1)) :=
      mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      calc
        _ = μ * (Real.exp z - 1 - z) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hrem hμ

private theorem chernoff_exponent {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 < t) :
    μ * (t / (2*(μ+t)))^2 - (t/(2*(μ+t)))*t ≤ -t^2/(4*(μ+t)) := by
  have hd : μ+t ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hμ ht)
  calc
    _ ≤ (μ+t) * (t/(2*(μ+t)))^2 - (t/(2*(μ+t)))*t := by
      exact sub_le_sub_right (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) _
    _ = _ := by field_simp; ring

theorem bernstein_of_transform (P : PMF Ω) (X : Ω → ℕ) (μ : ℝ) (hμ : 0 ≤ μ)
    (htr : ∀ s : ℝ, 0 < s → expect P (fun ω => s ^ X ω) ≤ Real.exp (μ * (s-1)))
    {t : ℝ} (ht : 0 < t) :
    probability P (fun ω => t ≤ |(X ω : ℝ)-μ|) ≤ 2*Real.exp (-t^2/(4*(μ+t))) := by
  let z := t/(2*(μ+t))
  have hd : 0 < 2*(μ+t) := by positivity
  have hz : 0 < z := div_pos ht hd
  have hz1 : z ≤ 1 := (div_le_one hd).2 (by linarith)
  have hzabs : |z| ≤ 1 := by rwa [abs_of_pos hz]
  have htail (a : ℝ) (ha : |a| ≤ 1) (ha2 : a^2 = z^2) :
      probability P (fun ω => z*t ≤ a*((X ω : ℝ)-μ)) ≤ Real.exp (-t^2/(4*(μ+t))) := by
    calc
      _ ≤ probability P (fun ω => Real.exp (z*t) ≤ Real.exp (a*((X ω : ℝ)-μ))) := by
        apply probability_mono
        intro ω hω
        exact Real.exp_le_exp.mpr hω
      _ ≤ expect P (fun ω => Real.exp (a*((X ω : ℝ)-μ))) / Real.exp (z*t) :=
        markov P (fun _ => Real.exp_nonneg _) (Real.exp_pos _)
      _ ≤ Real.exp (μ*z^2) / Real.exp (z*t) := by
        apply div_le_div_of_nonneg_right _ (Real.exp_nonneg _)
        simpa only [ha2] using centered_exp_of_transform P X μ hμ htr ha
      _ = Real.exp (μ*z^2-z*t) := (Real.exp_sub _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (chernoff_exponent hμ ht)
  have hu : probability P (fun ω => t ≤ (X ω : ℝ)-μ) ≤ Real.exp (-t^2/(4*(μ+t))) :=
    le_trans (probability_mono P (fun ω hω => mul_le_mul_of_nonneg_left hω hz.le))
      (htail z hzabs rfl)
  have hl : probability P (fun ω => t ≤ -((X ω : ℝ)-μ)) ≤ Real.exp (-t^2/(4*(μ+t))) := by
    apply le_trans _ (htail (-z) (by simpa using hzabs) (by ring))
    apply probability_mono
    intro ω hω
    nlinarith [mul_le_mul_of_nonneg_left hω hz.le]
  calc
    _ ≤ probability P (fun ω => t ≤ (X ω : ℝ)-μ ∨ t ≤ -((X ω : ℝ)-μ)) :=
      probability_mono P (fun _ hω => le_abs.mp hω)
    _ ≤ _ := probability_union_le P _ _
    _ ≤ _ := by linarith

theorem half_mean_of_transform (P : PMF Ω) (X : Ω → ℕ) (μ : ℝ)
    (htr : ∀ s : ℝ, 0 < s → expect P (fun ω => s ^ X ω) ≤ Real.exp (μ * (s-1))) :
    probability P (fun ω => (X ω : ℝ) ≤ μ/2) ≤ Real.exp (-chernoffConstant*μ) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp (-Real.log 2) = (1/2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hx (n : ℕ) : (1/2 : ℝ)^n = Real.exp (-Real.log 2 * (n : ℝ)) := by
    rw [mul_comm, Real.exp_nat_mul, hexp]
  calc
    _ ≤ probability P (fun ω => Real.exp (-Real.log 2 * (μ/2)) ≤ (1/2 : ℝ)^X ω) := by
      apply probability_mono
      intro ω hω
      rw [hx]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hω (by linarith))
    _ ≤ expect P (fun ω => (1/2 : ℝ)^X ω) / Real.exp (-Real.log 2 * (μ/2)) :=
      markov P (fun _ => by positivity) (Real.exp_pos _)
    _ ≤ Real.exp (μ*((1/2 : ℝ)-1)) / Real.exp (-Real.log 2 * (μ/2)) :=
      div_le_div_of_nonneg_right (htr _ (by norm_num)) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_sub]
      congr 1
      unfold chernoffConstant
      ring

theorem less_two_of_transform (P : PMF Ω) (X : Ω → ℕ) (μ : ℝ)
    (htr : ∀ s : ℝ, 0 < s → expect P (fun ω => s ^ X ω) ≤ Real.exp (μ * (s-1))) :
    probability P (fun ω => X ω < 2) ≤ 2*Real.exp (-μ/2) := by
  calc
    _ ≤ probability P (fun ω => (1/2 : ℝ) ≤ (1/2 : ℝ)^X ω) := by
      apply probability_mono
      intro ω hω
      have hx : X ω = 0 ∨ X ω = 1 := by omega
      rcases hx with hx | hx <;> norm_num [hx]
    _ ≤ expect P (fun ω => (1/2 : ℝ)^X ω) / (1/2 : ℝ) :=
      markov P (fun _ => by positivity) (by norm_num)
    _ ≤ Real.exp (μ*((1/2 : ℝ)-1)) / (1/2 : ℝ) :=
      div_le_div_of_nonneg_right (htr _ (by norm_num)) (by norm_num)
    _ = _ := by
      rw [show μ*((1/2 : ℝ)-1) = -μ/2 by ring]
      ring

end RiffleLowerV2.Thinning
