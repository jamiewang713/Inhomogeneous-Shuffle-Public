import RiffleLowerV2.Shared.Geometry
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Types
open TimeProfile

/-- The continuous value at zero is included in this definition. -/
def xlogx (x : ℝ) : ℝ := x * Real.log x

@[simp] theorem xlogx_zero : xlogx 0 = 0 := by simp [xlogx]

private theorem factorial_log_bounds_succ (n : ℕ) :
    0 ≤ Real.log ((n+1).factorial : ℝ) - xlogx (n+1) + (n+1 : ℝ) ∧
    Real.log ((n+1).factorial : ℝ) - xlogx (n+1) + (n+1 : ℝ) ≤
      Real.log (n+1)+1 := by
  induction n with
  | zero => norm_num [xlogx]
  | succ n ih =>
    have ha : 0 < (n : ℝ)+1 := by positivity
    have hb : 0 < (n : ℝ)+1+1 := by positivity
    have hu := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
    have hlu := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos ha hb)) hb.le
    have hqu : ((n : ℝ)+1)*(((n : ℝ)+1+1)/((n : ℝ)+1)-1) = 1 := by
      field_simp
      ring
    have hql : ((n : ℝ)+1+1)*(((n : ℝ)+1)/((n : ℝ)+1+1)-1) = -1 := by
      field_simp
      ring
    rw [hqu, Real.log_div hb.ne' ha.ne'] at hu
    rw [hql, Real.log_div ha.ne' hb.ne'] at hlu
    have hrec : Real.log ((n+1+1).factorial : ℝ) =
        Real.log ((n : ℝ)+1+1) + Real.log ((n+1).factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      norm_cast
    simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
    rw [hrec]
    dsimp [xlogx] at ih ⊢
    constructor <;> nlinarith [ih.1, ih.2]

/-- Two-sided logarithmic factorial control, with zero included. -/
theorem factorial_log_error (n : ℕ) :
    |Real.log (n.factorial : ℝ) - (xlogx n - (n : ℝ))| ≤
      Real.log ((n : ℝ)+1)+2 := by
  cases n with
  | zero => norm_num [xlogx]
  | succ n =>
    have h := factorial_log_bounds_succ n
    have hmono : Real.log ((n : ℝ)+1) ≤ Real.log ((n : ℝ)+1+1) :=
      Real.log_le_log (by positivity) (by linarith)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (by linarith [h.1])]
    linarith [h.2]

private theorem xlogx_sub_le_of_le {n x y : ℝ}
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hxy : x ≤ y) (hyn : y ≤ n)
    (hd : y - x ≤ 1) : xlogx y - xlogx x ≤ Real.log (n+1)+2 := by
  have hL : 0 ≤ Real.log (n+1) := Real.log_nonneg (by linarith)
  by_cases hx0 : x = 0
  · subst x
    have hy1 : y ≤ 1 := by linarith
    have hy0 : 0 ≤ y := hxy
    have := Real.mul_log_nonpos hy0 hy1
    simpa only [xlogx, zero_mul, sub_zero] using
      (show y * Real.log y ≤ Real.log (n+1)+2 by linarith)
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hyp : 0 < y := hxp.trans_le hxy
  have hratio : Real.log (y/x) ≤ y/x-1 :=
    Real.log_le_sub_one_of_pos (div_pos hyp hxp)
  have hmul := mul_le_mul_of_nonneg_left hratio hx
  have hquot : x * (y/x-1) = y-x := by field_simp
  rw [hquot, Real.log_div hyp.ne' hxp.ne'] at hmul
  have hlog : Real.log y ≤ Real.log (n+1) :=
    Real.log_le_log hyp (by linarith)
  have hd0 : 0 ≤ y-x := sub_nonneg.mpr hxy
  have hprod : (y-x)*Real.log y ≤ Real.log (n+1) :=
    calc
      _ ≤ (y-x)*Real.log (n+1) := mul_le_mul_of_nonneg_left hlog hd0
      _ ≤ 1*Real.log (n+1) := mul_le_mul_of_nonneg_right hd hL
      _ = _ := one_mul _
  dsimp [xlogx]
  nlinarith

private theorem xlogx_sub_rev_le_of_le {n x y : ℝ}
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hxy : x ≤ y) :
    xlogx x - xlogx y ≤ Real.log (n+1)+2 := by
  have hL : 0 ≤ Real.log (n+1) := Real.log_nonneg (by linarith)
  have hy : 0 ≤ y := hx.trans hxy
  by_cases hy1 : y ≤ 1
  · have hxlog := Real.mul_log_nonpos hx (hxy.trans hy1)
    have hylog := Real.self_sub_one_le_mul_log hy
    dsimp [xlogx]
    linarith
  have hy1' : 1 ≤ y := le_of_lt (lt_of_not_ge hy1)
  by_cases hx1 : x ≤ 1
  · have hxlog := Real.mul_log_nonpos hx hx1
    have hylog := Real.mul_log_nonneg hy1'
    dsimp [xlogx]
    linarith
  have hx1' : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
  have hp : x * Real.log x ≤ y * Real.log y :=
    mul_le_mul hxy (Real.log_le_log (by linarith) hxy)
      (Real.log_nonneg hx1') hy
  dsimp [xlogx]
  linarith

/-- A zero-safe modulus on a bounded interval for rounding by at most one. -/
theorem xlogx_rounding_bound {n x y : ℝ}
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hxn : x ≤ n)
    (hy : 0 ≤ y) (hyn : y ≤ n) (hround : |x-y| ≤ 1) :
    |xlogx x - xlogx y| ≤ Real.log (n+1)+2 := by
  rcases le_total x y with hxy | hyx
  · apply abs_le.mpr
    constructor
    · have h := xlogx_sub_le_of_le hn hx hxy hyn (by
        have := (abs_le.mp hround).1; linarith)
      linarith
    · exact xlogx_sub_rev_le_of_le hn hx hxy
  · apply abs_le.mpr
    constructor
    · have h := xlogx_sub_rev_le_of_le hn hy hyx
      linarith
    · exact xlogx_sub_le_of_le hn hy hyx hxn (abs_le.mp hround).2

/-- Scaling a probability vector, including total zero, in entropy form. -/
theorem entropy_scale_identity {k : ℕ} (n : ℕ) (q : Fin k → ℝ)
    (_hq : ∀ l, 0 ≤ q l) (hs : ∑ l, q l = 1) :
    (n : ℝ) * shannonEntropy q = xlogx n - ∑ l, xlogx ((n : ℝ)*q l) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hterm (l : Fin k) :
      xlogx ((n : ℝ)*q l) = (n : ℝ)*q l*Real.log n + (n : ℝ)*(q l*Real.log (q l)) := by
    by_cases hl : q l = 0
    · simp [hl]
    · dsimp [xlogx]
      rw [Real.log_mul hn0 hl]
      ring
  have hremove : shannonEntropy q = -∑ l, q l * Real.log (q l) := by
    unfold shannonEntropy
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : q l = 0 <;> simp [hl]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hs]
  rw [← Finset.mul_sum, hremove]
  simp [xlogx]

/-- The complete rounding loss, including empty cells. -/
theorem entropy_rounding_error {k : ℕ} (n : ℕ) (c : Fin k → ℕ) (q : Fin k → ℝ)
    (hc : ∑ l, c l = n) (hq : ∀ l, 0 ≤ q l) (hs : ∑ l, q l = 1)
    (hr : ∀ l, |(c l : ℝ)-(n : ℝ)*q l| ≤ 1) :
    |xlogx n - (∑ l, xlogx (c l)) - (n : ℝ)*shannonEntropy q| ≤
      (k : ℝ)*(Real.log ((n : ℝ)+1)+2) := by
  have hq1 (l : Fin k) : q l ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun i _ => hq i) (Finset.mem_univ l)
  have hc1 (l : Fin k) : c l ≤ n := by
    rw [← hc]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ l)
  have hterm (l : Fin k) :
      |xlogx ((n : ℝ)*q l) - xlogx (c l)| ≤ Real.log ((n : ℝ)+1)+2 := by
    rw [abs_sub_comm]
    exact xlogx_rounding_bound (by positivity) (by positivity) (by exact_mod_cast hc1 l)
      (mul_nonneg (by positivity) (hq l))
      (by simpa using mul_le_mul_of_nonneg_left (hq1 l) (show 0 ≤ (n : ℝ) by positivity))
      (hr l)
  rw [entropy_scale_identity n q hq hs]
  have hid : xlogx n - (∑ l, xlogx (c l)) -
      (xlogx n - ∑ l, xlogx ((n : ℝ)*q l)) =
      ∑ l, (xlogx ((n : ℝ)*q l)-xlogx (c l)) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  calc
    _ ≤ ∑ l, |xlogx ((n : ℝ)*q l)-xlogx (c l)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin k, (Real.log ((n : ℝ)+1)+2) :=
      Finset.sum_le_sum (fun l _ => hterm l)
    _ = _ := by simp [mul_add]

/-- The factorial expression has both lower and upper entropy estimates. -/
theorem multinomial_log_factorial_error {k : ℕ} (n : ℕ) (c : Fin k → ℕ)
    (hc : ∑ l, c l = n) :
    |(Real.log (n.factorial : ℝ) - ∑ l, Real.log ((c l).factorial : ℝ)) -
      (xlogx n - ∑ l, xlogx (c l))| ≤
      ((k : ℝ)+1)*(Real.log ((n : ℝ)+1)+2) := by
  have hc1 (l : Fin k) : c l ≤ n := by
    rw [← hc]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ l)
  have hcR : ∑ l, (c l : ℝ) = n := by exact_mod_cast hc
  have hterm (l : Fin k) :
      |Real.log ((c l).factorial : ℝ) - (xlogx (c l) - (c l : ℝ))| ≤
      Real.log ((n : ℝ)+1)+2 := by
    apply (factorial_log_error (c l)).trans
    have hlog : Real.log ((c l : ℝ)+1) ≤ Real.log ((n : ℝ)+1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (hc1 l) 1)
    linarith
  have hsum : |∑ l, (Real.log ((c l).factorial : ℝ) -
      (xlogx (c l) - (c l : ℝ)))| ≤
      (k : ℝ)*(Real.log ((n : ℝ)+1)+2) := by
    calc
      _ ≤ ∑ l, |Real.log ((c l).factorial : ℝ) -
          (xlogx (c l) - (c l : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin k, (Real.log ((n : ℝ)+1)+2) :=
        Finset.sum_le_sum (fun l _ => hterm l)
      _ = _ := by simp [mul_add]
  have hid : (Real.log (n.factorial : ℝ) - ∑ l, Real.log ((c l).factorial : ℝ)) -
      (xlogx n - ∑ l, xlogx (c l)) =
      (Real.log (n.factorial : ℝ) - (xlogx n - (n : ℝ))) -
      ∑ l, (Real.log ((c l).factorial : ℝ) - (xlogx (c l) - (c l : ℝ))) := by
    simp only [Finset.sum_sub_distrib, hcR]
    ring
  rw [hid]
  calc
    _ ≤ |Real.log (n.factorial : ℝ) - (xlogx n - (n : ℝ))| +
        |∑ l, (Real.log ((c l).factorial : ℝ) - (xlogx (c l) - (c l : ℝ)))| :=
      abs_sub _ _
    _ ≤ (Real.log ((n : ℝ)+1)+2) + (k : ℝ)*(Real.log ((n : ℝ)+1)+2) :=
      add_le_add (factorial_log_error n) hsum
    _ = _ := by ring

/-- A uniform finite lower and upper log-count estimate after rounding. -/
theorem multinomial_log_entropy_error {k : ℕ} (n : ℕ) (c : Fin k → ℕ) (q : Fin k → ℝ)
    (hc : ∑ l, c l = n) (hq : ∀ l, 0 ≤ q l) (hs : ∑ l, q l = 1)
    (hr : ∀ l, |(c l : ℝ)-(n : ℝ)*q l| ≤ 1) :
    |(Real.log (n.factorial : ℝ) - ∑ l, Real.log ((c l).factorial : ℝ)) -
      (n : ℝ)*shannonEntropy q| ≤
      (2*(k : ℝ)+1)*(Real.log ((n : ℝ)+1)+2) := by
  calc
    _ ≤ |(Real.log (n.factorial : ℝ) - ∑ l, Real.log ((c l).factorial : ℝ)) -
          (xlogx n - ∑ l, xlogx (c l))| +
        |(xlogx n - ∑ l, xlogx (c l)) - (n : ℝ)*shannonEntropy q| :=
      abs_sub_le _ _ _
    _ ≤ ((k : ℝ)+1)*(Real.log ((n : ℝ)+1)+2) +
        (k : ℝ)*(Real.log ((n : ℝ)+1)+2) :=
      add_le_add (multinomial_log_factorial_error n c hc)
        (entropy_rounding_error n c q hc hq hs hr)
    _ = _ := by ring

end RiffleLowerV2.Types
