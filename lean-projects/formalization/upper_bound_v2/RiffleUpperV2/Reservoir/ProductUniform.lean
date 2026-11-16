import RiffleUpperV2.Reservoir.ProductUpper
import RiffleUpperV2.Reservoir.Capacity
import RiffleUpperV2.Reservoir.ReserveUniform

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile

/-- One explicit regular-coordinate error works for every good residual
configuration. -/
theorem regular_error_budget {n c m : ℕ} (hn : 1≤n) {g τ : ℝ}
    (hg : 0<g) (hτ : 0<τ) (hc : g*n≤c) :
    (n:ℝ)^((2:ℝ)/3)+2 ≤ ((c+m:ℕ):ℝ)*τ*((3/(g*τ))/(n:ℝ)^((1:ℝ)/3)) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hpow : 1≤(n:ℝ)^((2:ℝ)/3) := Real.one_le_rpow hn1 (by norm_num)
  have hcp : g*n≤(c+m:ℕ) := hc.trans (by exact_mod_cast Nat.le_add_right c m)
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcp hτ.le)
    (by positivity : 0≤(3/(g*τ))/(n:ℝ)^((1:ℝ)/3))
  have heq : (g*n)*τ*((3/(g*τ))/(n:ℝ)^((1:ℝ)/3))=3*(n:ℝ)^((2:ℝ)/3) := by
    have he : (n:ℝ)^((2:ℝ)/3)*(n:ℝ)^((1:ℝ)/3)=(n:ℝ) := by
      rw [← Real.rpow_add hn0]
      norm_num
    have hnq : (n:ℝ)^((1:ℝ)/3)≠0 := ne_of_gt (Real.rpow_pos_of_pos hn0 _)
    field_simp
    nlinarith
  rw [heq] at hmul
  linarith

/-- Exact residual weights satisfy the regular/rare product bound uniformly
for every finite selection of logarithmically many coordinates. -/
theorem residual_product_upper_uniform (g τ T : ℝ) (hg : 0<g) (hg1 : g<1)
    (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ c m : ℕ,
      g*n≤c → m≤2 → ∀ (ι : Type*) (J : Finset ι) (p : ι→ℝ) (R : ι→ℕ),
      (J.card:ℝ)≤T*Real.log (n:ℝ) →
      (∀ j∈J, 0≤p j ∧ p j≤1) → (∀ j∈J, R j≤c+m) →
      (∀ j∈J, (R j:ℝ)≤n*p j) →
      (∀ j∈J, |(R j:ℝ)-(c:ℝ)*p j|≤(n:ℝ)^((2:ℝ)/3)+m) →
      (∏ j∈J, RiffleLowerV2.falling (R j) m / RiffleLowerV2.falling (c+m) m) ≤
        2^m*(∏ j∈J, p j)^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ))) := by
  obtain ⟨N0,hN01,hN0⟩ := eventual_logarithmic_error (3/(g*τ)) T (by positivity) hT
  refine ⟨N0,hN01,?_⟩
  intro n hn c m hc hm ι J p R hJ hp hR hcut hcount
  have hn1 : 1≤n := hN01.trans hn
  have hn0 : 0<n := by omega
  let δ : ℝ := (3/(g*τ))/(n:ℝ)^((1:ℝ)/3)
  have hδ : 0≤δ := by dsimp [δ]; positivity
  apply product_power_envelope J (c+m) m R p _ δ (fun j hj => (hp j hj).1) hR hδ _
    (hN0 n hn J.card hJ)
  intro j hj
  apply coordinate_power_envelope (hp j hj).1 (hp j hj).2 hτ hg
    (rareExponent_nonneg hg hg1 hτ (hτg.trans hg1)) hα
    (rareExponent_identity hg hτ (hτg.trans hg1)) hδ
  · intro hreg
    apply regular_coordinate_ratio hreg (hp j hj).1 hτ hδ hm
      (by
        have hcp : (0:ℝ)<c := lt_of_lt_of_le (by positivity) hc
        have : 0<c := by exact_mod_cast hcp
        omega)
      (regular_error_budget hn1 hg hτ hc) (hcount j hj)
  · intro _
    exact rare_coordinate_ratio hg hn0 (hp j hj).1 (hcut j hj)
      (hc.trans (by exact_mod_cast Nat.le_add_right c m))

end RiffleUpperV2.Reservoir
