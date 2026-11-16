import Contracts.v1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorial.BigOperators

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiffleLowerV2.Factorial
open TimeProfile

/-- A quantitative logarithm estimate, including the zero perturbation. -/
theorem abs_log_one_sub_le {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 1/2) :
    |Real.log (1-x)| ≤ 2*x := by
  have hp : 0 < 1-x := by linarith
  have hu : Real.log (1-x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hi : (1-x)⁻¹ ≤ 1+2*x := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).2
    nlinarith
  rw [abs_of_nonpos hu]
  linarith

/-- Passing from a logarithmic ratio bound to a relative error. -/
theorem relative_error_of_log {x y e : ℝ} (hx : 0 < x) (hy : 0 < y)
    (he : |Real.log (x/y)| ≤ e) (he1 : e ≤ 1) :
    |x-y| ≤ 2*e*y := by
  have ht := Real.abs_exp_sub_one_le (he.trans he1)
  rw [Real.exp_log (div_pos hx hy)] at ht
  have hxy : |x-y| = |x/y-1| * y := by
    calc
      |x-y| = |(x/y-1)*y| := by congr 1; field_simp
      _ = |x/y-1| * y := by rw [abs_mul, abs_of_pos hy]
  rw [hxy]
  exact mul_le_mul_of_nonneg_right (ht.trans (by linarith)) hy.le

/-- Falling factorial divided by its power benchmark. -/
def fallingCorrection (n r : ℕ) : ℝ := falling n r / (n : ℝ)^r

@[simp] theorem fallingCorrection_zero (n : ℕ) : fallingCorrection n 0 = 1 := by
  simp [fallingCorrection, falling]

theorem fallingCorrection_pos {n r : ℕ} (hn : 0 < n) (hr : r ≤ n) :
    0 < fallingCorrection n r := by
  apply div_pos
  · unfold falling
    exact_mod_cast (Nat.descFactorial_pos.mpr hr)
  · positivity

theorem fallingCorrection_succ {n r : ℕ} (hn : 0 < n) (hr : r ≤ n) :
    fallingCorrection n (r+1) = fallingCorrection n r * (1-(r : ℝ)/n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [fallingCorrection, falling, Nat.descFactorial_succ, Nat.cast_mul,
    Nat.cast_sub hr, pow_succ]
  field_simp

/-- Uniform finite bound with explicit positivity domain; no asymptotic premise. -/
theorem log_fallingCorrection_bound {n r : ℕ} (hn : 0 < n)
    (hr : 2*r ≤ n) : |Real.log (fallingCorrection n r)| ≤ (r : ℝ)^2/n := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hrn : r ≤ n := by omega
    have hr2 : 2*r ≤ n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hrR : (r : ℝ)/n ≤ 1/2 := by
      apply (div_le_iff₀ hnR).2
      have : (2 : ℝ)*r ≤ n := by exact_mod_cast hr2
      linarith
    have hpos : 0 < 1-(r : ℝ)/n := by linarith
    rw [fallingCorrection_succ hn hrn,
      Real.log_mul (fallingCorrection_pos hn hrn).ne' hpos.ne']
    calc
      |Real.log (fallingCorrection n r) + Real.log (1-(r : ℝ)/n)| ≤
          |Real.log (fallingCorrection n r)| + |Real.log (1-(r : ℝ)/n)| := abs_add_le _ _
      _ ≤ (r : ℝ)^2/n + 2*((r : ℝ)/n) :=
        add_le_add (ih hr2) (abs_log_one_sub_le (by positivity) hrR)
      _ ≤ ((r+1 : ℕ) : ℝ)^2/n := by
        push_cast
        apply (le_div_iff₀ hnR).2
        field_simp
        nlinarith

/-- Logarithmic comparison for removing a bounded number of elements. -/
theorem log_sub_ratio_bound {n u : ℕ} (hn : 0 < n) (hu : 2*u ≤ n) :
    |Real.log (((n-u : ℕ) : ℝ)/(n : ℝ))| ≤ 2*(u : ℝ)/n := by
  have hun : u ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huR : (u : ℝ)/n ≤ 1/2 := by
    apply (div_le_iff₀ hnR).2
    have : (2 : ℝ)*u ≤ n := by exact_mod_cast hu
    linarith
  rw [Nat.cast_sub hun, sub_div, div_self hnR.ne']
  simpa only [mul_div_assoc] using abs_log_one_sub_le (by positivity) huR

end RiffleLowerV2.Factorial
