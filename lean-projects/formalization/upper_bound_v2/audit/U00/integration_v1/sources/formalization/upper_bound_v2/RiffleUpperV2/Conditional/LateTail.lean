import RiffleUpperV2.Conditional.TailMass
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter Topology
namespace RiffleUpperV2.Conditional

/-- The late-short-tail classification uses a uniform threshold chosen before
all cut arrays and prefixes. Its rho*log k cost is retained explicitly. -/
theorem lateShort_tiny_uniform (k : ℕ) (hk : 1 ≤ k) (η ρ ξ : ℝ)
    (hρ : 0 ≤ ρ) (hgap : ξ < η-ρ*Real.log (k : ℝ)) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ n K : ℕ,
      ∀ cuts : Cuts k n K, ∀ hn : 0 < n, ∀ x : Prefix k K,
      K-x.1.val ≤ Exploration.windowLength N ρ →
      empiricalBeta N 0 cuts hn K ≤ -η → prefixMean cuts x < (N : ℝ)^(-ξ) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(η-ρ*Real.log (k : ℝ)-ξ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp (ht.eventually_gt_atTop ((k : ℝ)^2))
  refine ⟨max N0 2,le_max_right _ _,?_⟩
  intro N hN n K cuts hn x hshort hmargin
  have hN2 : 2 ≤ N := (le_max_right N0 2).trans hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hc := hN0 N ((le_max_left _ _).trans hN)
  apply (lateShortMean_le hk hN2 cuts hn x hρ hshort hmargin).trans_lt
  calc
    _ < (N : ℝ)^(η-ρ*Real.log (k : ℝ)-ξ)*(N : ℝ)^(-η+ρ*Real.log (k : ℝ)) :=
      mul_lt_mul_of_pos_right hc (Real.rpow_pos_of_pos hn0 _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end RiffleUpperV2.Conditional
