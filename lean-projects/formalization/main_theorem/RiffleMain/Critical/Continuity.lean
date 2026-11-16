import RiffleMain.Critical.Signs
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

noncomputable section
open Set MeasureTheory
namespace RiffleMain.Critical
open TimeProfile RiffleLowerV2 RiffleUpperV2 RiffleUpperV2.ProfileUpper

theorem reducedMargin_horizon {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : RiffleLowerV2.ScalarIntegrable μ P T) :
    0 ≤ reducedMargin μ S - reducedMargin μ T ∧
      reducedMargin μ S - reducedMargin μ T ≤ 8 * Real.log (k : ℝ) * (T-S) := by
  have hT := hS.trans hST
  have hl := RiffleUpperV2.ProfileUpper.macroLambda_horizon hk hT hS hST hI
  have hb := beta_decay hS hST hI
  have ha := scalar_bounds hT hI.2.1 (RiffleLowerV2.ProfileTransfer.profileMaxCost_bounds hk μ)
    hS hST le_rfl
  have haBound := ha.2
  change integratedMaxCost μ S T ≤ Real.log (k : ℝ) * (T-S) at haBound
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hgap : 0 ≤ Real.log (k : ℝ) * (T-S) := mul_nonneg hlog (sub_nonneg.mpr hST)
  have hbT : RiffleLowerV2.macroBeta μ T ≤ reducedMargin μ T := le_max_left _ _
  have hlT : RiffleLowerV2.macroLambda1 μ T ≤ reducedMargin μ T := le_max_right _ _
  have hm : reducedMargin μ S ≤ reducedMargin μ T + 8 * Real.log (k : ℝ) * (T-S) :=
    max_le (by linarith) (by linarith [hl.2])
  exact ⟨sub_nonneg.mpr (marginMonotonicity hk hS hST hI), by linarith⟩

theorem reducedMargin_abs_sub_le {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    |reducedMargin μ S - reducedMargin μ T| ≤ 8 * Real.log (k : ℝ) * |S-T| := by
  have ordered : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y →
      |reducedMargin μ x - reducedMargin μ y| ≤ 8 * Real.log (k : ℝ) * |x-y| := by
    intro x y hx hxy
    by_cases hy0 : y = 0
    · have hx0 : x = 0 := by linarith
      simp [hy0, hx0]
    · obtain ⟨P, hP⟩ := hI y (lt_of_le_of_ne (hx.trans hxy) (Ne.symm hy0))
      have h := reducedMargin_horizon hk hx hxy hP
      rw [abs_of_nonneg h.1, abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith [h.2]
  rcases le_total S T with hST | hTS
  · exact ordered hS hST
  · simpa only [abs_sub_comm] using ordered hT hTS

theorem reducedMargin_continuousOn {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : LocallyScalarIntegrable μ) : ContinuousOn (reducedMargin μ) (Ici (0 : ℝ)) := by
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  let C : NNReal := ⟨8 * Real.log (k : ℝ), by positivity⟩
  have hLip : LipschitzOnWith C
      (reducedMargin μ) (Ici (0 : ℝ)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro S hS T hT
    change |reducedMargin μ S - reducedMargin μ T| ≤ 8 * Real.log (k : ℝ) * |S-T|
    exact reducedMargin_abs_sub_le hk hI hS hT
  exact hLip.continuousOn

end RiffleMain.Critical
