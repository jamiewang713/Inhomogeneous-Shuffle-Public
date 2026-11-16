import RiffleLowerV2.Factorial.Ratios

noncomputable section
open scoped Topology
open Filter
namespace RiffleLowerV2.Factorial
open TimeProfile

theorem momentCutoff_ratio_tendsto :
    Tendsto (fun N : ℕ => 2*(N : ℝ)^(1/5 : ℝ)/N) atTop (𝓝 0) := by
  have hh : Tendsto (fun x : ℝ => 2*x^(-(4/5 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4/5)).const_mul 2
  have hr : Tendsto (fun x : ℝ => 2*x^(1/5 : ℝ)/x) atTop (𝓝 0) := by
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [mul_div_assoc, ← Real.rpow_sub_one hx.ne']
    norm_num
  exact hr.comp tendsto_natCast_atTop_atTop

theorem momentBudget_tendsto (c C : ℝ) :
    Tendsto (fun N : ℕ => (2/c)*(C*logScale N+1)*((N : ℝ)^(1/5 : ℝ))^2/N)
      atTop (𝓝 0) := by
  have ha : Tendsto (fun x : ℝ => Real.log x / x^(3/5 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3/5)).tendsto_div_nhds_zero
  have hb : Tendsto (fun x : ℝ => 1 / x^(3/5 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/5))
  have hh : Tendsto (fun x : ℝ => (2/c)*(C*(Real.log x / x^(3/5 : ℝ)) + 1/x^(3/5 : ℝ)))
      atTop (𝓝 0) := by
    simpa using ((ha.const_mul C).add hb).const_mul (2/c)
  have hr : Tendsto (fun x : ℝ => (2/c)*(C*Real.log x+1)*(x^(1/5 : ℝ))^2/x)
      atTop (𝓝 0) := by
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hp : (x^(1/5 : ℝ))^2/x = 1/x^(3/5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
      rw [← Real.rpow_sub_one hx.ne']
      norm_num
      rw [Real.rpow_neg hx.le]
    calc
      (2/c) * (C * (Real.log x / x^(3/5 : ℝ)) + 1/x^(3/5 : ℝ)) =
          (2/c)*(C*Real.log x+1)*(1/x^(3/5 : ℝ)) := by ring
      _ = (2/c)*(C*Real.log x+1)*(x^(1/5 : ℝ))^2/x := by rw [← hp]; ring
  exact hr.comp tendsto_natCast_atTop_atTop

/-- A single uniform threshold supplies both the positivity and small-log budgets. -/
theorem eventual_factorial_budgets {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0,
      2*(N : ℝ)^(1/5 : ℝ) ≤ c*N ∧
      (2/c)*(C*logScale N+1)*((N : ℝ)^(1/5 : ℝ))^2/N ≤ 1 := by
  have h1 := momentCutoff_ratio_tendsto.eventually (eventually_lt_nhds hc)
  have h2 := (momentBudget_tendsto c C).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (h1.and h2)
  refine ⟨max N1 2, le_max_right _ _, ?_⟩
  intro N hN
  have hNN : N1 ≤ N := (le_max_left _ _).trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact ⟨((div_lt_iff₀ hNp).mp (hN1 N hNN).1).le, (hN1 N hNN).2.le⟩

end RiffleLowerV2.Factorial
