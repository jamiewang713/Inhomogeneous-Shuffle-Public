import RiffleUpperV2.Reservoir.PrefixConditional
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Algebra.Order.Ring.Pow

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Reservoir

/-- A lower bound for one or two ordered marked draws. The extra unit covers
the loss in the second falling-factorial factor. -/
theorem falling_ratio_lower_one_two {M R m : ℕ} (hM : 2 ≤ M) (hm : m=1 ∨ m=2)
    {q : ℝ} (hq : 0 ≤ q) (hR : (M : ℝ)*q+1 ≤ R) :
    q^m ≤ RiffleLowerV2.falling R m / RiffleLowerV2.falling M m := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  rcases hm with rfl | rfl
  · simp only [pow_one, RiffleLowerV2.falling, Nat.descFactorial_one]
    apply (le_div_iff₀ hMp).mpr
    nlinarith
  · simp only [RiffleLowerV2.falling, Nat.cast_descFactorial_two]
    have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hM1 : (0 : ℝ) < (M : ℝ)-1 := by linarith
    apply (le_div_iff₀ (mul_pos hMp hM1)).mpr
    have hRq : (M : ℝ)*q ≤ (R : ℝ) := by linarith
    have hR1 : (M : ℝ)*q ≤ (R : ℝ)-1 := by linarith
    have hp := mul_le_mul hRq hR1 (mul_nonneg hMp.le hq) (by positivity : (0 : ℝ) ≤ R)
    have hs : q^2 * ((M : ℝ)*((M : ℝ)-1)) ≤ ((M : ℝ)*q)^2 := by nlinarith [sq_nonneg q]
    nlinarith

theorem reserve_coordinate_lower {c R m : ℕ} (hc : 1 ≤ c) (hm : m=1 ∨ m=2)
    {p d δ err : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hd : d ≤ p)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbudget : err+5 ≤ (c : ℝ)*δ*d)
    (hR : |(R : ℝ)-(c : ℝ)*p| ≤ err+m) :
    (p*(1-δ))^m ≤ RiffleLowerV2.falling R m / RiffleLowerV2.falling (c+m) m := by
  have hmn : m ≤ 2 := by rcases hm with rfl | rfl <;> omega
  have hmn' : (m : ℝ) ≤ 2 := by exact_mod_cast hmn
  have hmp : (m : ℝ)*p ≤ 2 := by
    calc
      _ ≤ (m : ℝ)*1 := mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg _)
      _ ≤ 2 := by simpa only [mul_one] using (show (m : ℝ) ≤ 2 by exact_mod_cast hmn)
  have hb : err+5 ≤ (c : ℝ)*δ*p := hbudget.trans
    (mul_le_mul_of_nonneg_left hd (mul_nonneg (Nat.cast_nonneg _) hδ0))
  have hlo := (abs_le.mp hR).1
  have hterm : 0 ≤ (m : ℝ)*p*δ := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hp0) hδ0
  apply falling_ratio_lower_one_two (by rcases hm with rfl | rfl <;> omega) hm
    (mul_nonneg hp0 (sub_nonneg.mpr hδ1))
  push_cast
  nlinarith

/-- A finite reserve denominator bound with an explicit error budget. This
is the d^m/2 constant of the source, uniform in the selected coordinates. -/
theorem reserve_product_lower {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (D c m : ℕ) (hD : 1 ≤ D) (hc : 1 ≤ c) (hm : m=1 ∨ m=2)
    (hcard : J.card ≤ D) (p : ι → ℝ) (R : ι → ℕ) (d err : ℝ)
    (hd : 0 < d) (hp : ∀ j ∈ J, 0 ≤ p j ∧ p j ≤ 1)
    (hmass : d ≤ ∏ j ∈ J, p j)
    (hbudget : err+5 ≤ (c : ℝ) * (1 / (4*D)) * d)
    (hR : ∀ j ∈ J, |(R j : ℝ)-(c : ℝ)*p j| ≤ err+m) :
    d^m/2 ≤ ∏ j ∈ J,
      RiffleLowerV2.falling (R j) m / RiffleLowerV2.falling (c+m) m := by
  let δ : ℝ := 1/(4*D)
  have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; apply (div_le_iff₀ (by positivity)).mpr; nlinarith
  have hcoord (j : ι) (hj : j ∈ J) : d ≤ p j := by
    apply hmass.trans
    have hh := Finset.prod_le_prod_of_subset_of_le_one
      (s := {j}) (t := J) (f := p) (by simpa using hj)
      (fun i hi => (hp i hi).1) (fun i hi _ => (hp i hi).2)
    simpa only [Finset.prod_singleton] using hh
  have hlow : ∏ j ∈ J, (p j*(1-δ))^m ≤
      ∏ j ∈ J, RiffleLowerV2.falling (R j) m / RiffleLowerV2.falling (c+m) m := by
    apply Finset.prod_le_prod
    · intro j hj
      exact pow_nonneg (mul_nonneg (hp j hj).1 (sub_nonneg.mpr hδ1)) _
    · intro j hj
      exact reserve_coordinate_lower hc hm (hp j hj).1 (hp j hj).2 (hcoord j hj)
        hδ0 hδ1 hbudget (hR j hj)
  have hmn : m ≤ 2 := by rcases hm with rfl | rfl <;> omega
  have hexp : m*J.card ≤ 2*D := Nat.mul_le_mul hmn hcard
  have hbern : 1-(m*J.card : ℕ)*δ ≤ (1-δ)^(m*J.card) := by
    simpa only [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -δ) (by linarith : -2 ≤ -δ) (m*J.card))
  have hhalf : (1:ℝ)/2 ≤ (1-δ)^(m*J.card) := by
    apply le_trans _ hbern
    have hexp' : ((m*J.card : ℕ) : ℝ) ≤ 2*D := by exact_mod_cast hexp
    have heq : (2*(D : ℝ))*δ = 1/2 := by dsimp [δ]; field_simp; ring
    have hh := mul_le_mul_of_nonneg_right hexp' hδ0
    rw [heq] at hh
    linarith
  have hmasspow : d^m ≤ (∏ j ∈ J, p j)^m := pow_le_pow_left₀ hd.le hmass m
  apply le_trans _ hlow
  rw [Finset.prod_pow, Finset.prod_mul_distrib, mul_pow, Finset.prod_const, ← pow_mul]
  have hh := mul_le_mul hmasspow hhalf (by norm_num) (pow_nonneg (Finset.prod_nonneg (fun j hj => (hp j hj).1)) m)
  simpa only [mul_comm m J.card, div_eq_mul_inv, one_mul] using hh

end RiffleUpperV2.Reservoir
