import RiffleMain.RandomLower.CommonEvent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
set_option autoImplicit false
open scoped Topology
open RiffleLowerV2 TimeProfile Filter
open RiffleLowerV2.EmpiricalLower
namespace RiffleMain.RandomLower

/-- The number of arrays is quasipolynomial, and the null scan error is stretched
exponential. This estimate pays for the full union over count arrays and translates. -/
theorem array_scan_error_tendsto (k : ℕ) (T c : ℝ) (hT : 0 < T) (hc : 0 < c) :
    Tendsto (fun N : ℕ => ((N : ℝ)+1)^(k*horizonDepth N T+1) *
      Real.exp (-(N : ℝ)^c)) atTop (𝓝 0) := by
  let C : ℝ := 2*((k : ℝ)*T+1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hc).bound
    (show 0 < 1/(2*C) by positivity)
  have hsmall := tendsto_natCast_atTop_atTop.eventually hlo
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  have henv : Tendsto (fun N : ℕ => Real.exp (-(1/2 : ℝ)*(N : ℝ)^c))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      power_mul_stretchedExp_tendsto 0 c (1/2) hc (by norm_num)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => by positivity)) _ henv
  filter_upwards [hsmall, hlog, eventually_ge_atTop (2 : ℕ)] with N hsmall hlog hN
  change 1 ≤ Real.log (N : ℝ) at hlog
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hplus : (0 : ℝ) < (N : ℝ)+1 := by positivity
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hlogplus0 : 0 ≤ Real.log ((N : ℝ)+1) := Real.log_nonneg (by linarith)
  have hlogplus : Real.log ((N : ℝ)+1) ≤ 2*Real.log (N : ℝ) := by
    have h := Real.log_le_log hplus (show (N : ℝ)+1 ≤ (N : ℝ)^2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hdepth : (horizonDepth N T : ℝ) ≤ T*Real.log (N : ℝ) :=
    Nat.floor_le (mul_nonneg hT.le hlog0)
  have hcoeff : ((k*horizonDepth N T+1 : ℕ) : ℝ) ≤
      (k : ℝ)*T*Real.log (N : ℝ)+1 := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hdepth (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hpre : ((k*horizonDepth N T+1 : ℕ) : ℝ)*Real.log ((N : ℝ)+1) ≤
      C*(Real.log (N : ℝ))^2 := by
    have hmul := mul_le_mul hcoeff hlogplus hlogplus0
      (show 0 ≤ (k : ℝ)*T*Real.log (N : ℝ)+1 by positivity)
    have hsq : Real.log (N : ℝ) ≤ (Real.log (N : ℝ))^2 := by nlinarith
    dsimp [C]
    nlinarith
  have hsmall' : (Real.log (N : ℝ))^2 ≤ (1/(2*C))*(N : ℝ)^c := by
    simpa only [Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log (N : ℝ))),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) c)] using hsmall
  have hsmallC := mul_le_mul_of_nonneg_left hsmall' hC.le
  have hid : C*((1/(2*C))*(N : ℝ)^c) = (N : ℝ)^c/2 := by
    field_simp [hC.ne']
  rw [hid] at hsmallC
  have hpow : ((N : ℝ)+1)^(k*horizonDepth N T+1) =
      Real.exp (((k*horizonDepth N T+1 : ℕ) : ℝ)*Real.log ((N : ℝ)+1)) := by
    rw [Real.exp_nat_mul, Real.exp_log hplus]
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

theorem commonNullError_tendsto (k : ℕ) (T etaLargest etaCold : ℝ)
    (hT : 0 < T) (hl : 0 < etaLargest) (hc : 0 < etaCold) :
    Tendsto (fun N => commonNullError k N T etaLargest etaCold) atTop (𝓝 0) := by
  have hr := largestRunError_tendsto (runMargin etaLargest etaCold) (runMargin_pos hl hc)
  have ha := array_scan_error_tendsto k T (coldNullExponent etaCold) hT
    (coldNullExponent_pos hc)
  convert hr.add ha using 1
  · funext N
    unfold commonNullError coldNullError
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  · norm_num

end RiffleMain.RandomLower
