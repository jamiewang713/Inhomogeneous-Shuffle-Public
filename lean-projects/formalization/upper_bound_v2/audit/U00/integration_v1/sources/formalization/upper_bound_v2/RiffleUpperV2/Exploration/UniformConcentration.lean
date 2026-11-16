import RiffleUpperV2.Exploration.GuardConcentration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exploration
open RiffleLowerV2.Thinning Filter

/-- Finite full-H estimate, including all guards, outside counts and later counts. -/
theorem uniformConcentration_finite {k n L : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0 < n) (hk : 1 ≤ k) (D : ℕ) {g ξ : ℝ} (hg : 0 < g)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hscale : 2*(k : ℝ)^D/reserveMass k D g ≤ (n : ℝ)^(ξ/3)) :
    probability (fixedCountPMF cuts) (fun ω => ¬ concentrationEvent cuts D g ξ ω) ≤
      2 * ((2:ℝ)^k)^(L+1) * Real.exp (-(n : ℝ)^(ξ/3)/24) := by
  apply (probability_mono (fixedCountPMF cuts) (fun ω h => ?_)).trans
    (allCylinderFailure cuts hn hξ)
  exact fun hc => h (allCylinder_implies_concentration cuts hn hk D hg hξ1 hscale hc)

theorem cylinder_testCount_polynomial {k n K : ℕ} {T : ℝ} (hn : 0 < n)
    (hT : 0 ≤ T) (hK : (K : ℝ) ≤ T*Real.log (n : ℝ)) :
    ((2:ℝ)^k)^K ≤ (n : ℝ)^((k : ℝ)*T*Real.log 2) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_natCast ((2:ℝ)^k), Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hn0]
  rw [Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hp : 0 ≤ (k : ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hh := mul_le_mul_of_nonneg_left hK hp
  nlinarith

/-- Full source H concentration, with constants and threshold fixed before arrays.
This theorem does not require a margin or a good cluster: those are needed elsewhere. -/
theorem uniformConcentration (k : ℕ) (hk : 1 ≤ k) (D : ℕ) (T g ξ : ℝ)
    (hT : 0 < T) (hg : 0 < g) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ (n : ℕ), N0 ≤ n → ∀ L : ℕ, ((L+1 : ℕ) : ℝ) ≤ T*Real.log (n : ℝ) →
      ∀ cuts : Cuts k n (L+1),
      probability (fixedCountPMF cuts) (fun ω => ¬ concentrationEvent cuts D g ξ ω) ≤ badBound n ξ A c := by
  let α : ℝ := (k : ℝ)*T*Real.log 2
  let A : ℝ := 2+α
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hA : 0 < A := by dsimp [A]; linarith
  have hevent : ∀ᶠ n : ℕ in atTop, 2*(k : ℝ)^D/reserveMass k D g ≤ (n : ℝ)^(ξ/3) :=
    ((tendsto_rpow_atTop (by linarith : 0 < ξ/3)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hevent
  refine ⟨A, 1/24, hA, by norm_num, max N0 1, le_max_right _ _, ?_⟩
  intro n hn L hL cuts
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hn0 : 0 < n := by omega
  have hf := uniformConcentration_finite cuts hn0 hk D hg hξ.le hξ1
    (hN0 n ((le_max_left _ _).trans hn))
  apply hf.trans
  have hcount := cylinder_testCount_polynomial (k := k) hn0 hT.le hL
  have hpow : (n : ℝ)^α ≤ (n : ℝ)^A :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by dsimp [A]; linarith)
  have hpoly : 2*((2:ℝ)^k)^(L+1) ≤ A*(n : ℝ)^A := by
    apply (mul_le_mul_of_nonneg_left hcount (by norm_num)).trans
    exact mul_le_mul (by dsimp [A]; linarith) hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hA.le
  unfold badBound
  have he : -(n : ℝ)^(ξ/3)/24 = -(1/24:ℝ)*(n : ℝ)^(ξ/3) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)

end RiffleUpperV2.Exploration
