import RiffleUpperV2.ProfileUpper.Dominance

set_option autoImplicit false

/-! Strict horizon decay for the manuscript's two reduced margins. -/
noncomputable section
open Set MeasureTheory
namespace RiffleMain.Critical
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer
open RiffleUpperV2 RiffleUpperV2.ProfileUpper

theorem maxCost_split {k : ℕ} {μ : TimeLaw k} {P : BorelPartition k}
    {T r s t : ℝ} (hT : 0 ≤ T) (hI : RiffleLowerV2.ScalarIntegrable μ P T)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    integratedMaxCost μ r t = integratedMaxCost μ r s + integratedMaxCost μ s t := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (scalar_restrict hT hI.2.1 hr hrs (hst.trans ht))
    (scalar_restrict hT hI.2.1 (hr.trans hrs) hst ht)).symm

theorem psi_split {k : ℕ} {μ : TimeLaw k} {P : BorelPartition k}
    {T r s t θ : ℝ} (hT : 0 ≤ T) (hI : RiffleLowerV2.ScalarIntegrable μ P T)
    (hθ : θ ∈ Icc (2 : ℝ) 4)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    integratedPsi μ θ r t = integratedPsi μ θ r s + integratedPsi μ θ s t := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (scalar_restrict hT (hI.2.2 θ hθ) hr hrs (hst.trans ht))
    (scalar_restrict hT (hI.2.2 θ hθ) (hr.trans hrs) hst ht)).symm

theorem maxCost_nonneg {k : ℕ} (hk : 2 ≤ k) (μ : TimeLaw k)
    {r s : ℝ} (hrs : r ≤ s) : 0 ≤ integratedMaxCost μ r s :=
  intervalIntegral.integral_nonneg_of_forall hrs (fun t => (profileMaxCost_bounds hk μ t).1)

/-- Each part removed by clipping contributes at least twice its maximal-pile cost. -/
theorem macroF_clip_decay {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T S : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : RiffleLowerV2.ScalarIntegrable μ P T) (su : ℝ × ℝ) (hsu : su ∈ triangle T)
    (θ : ℝ) (hθ : θ ∈ Icc (3 : ℝ) 4) :
    macroF μ T θ su.1 su.2 ≤
      macroF μ S θ (min su.1 S) (min su.2 S) - 2 * integratedMaxCost μ S T := by
  have hT := hS.trans hST
  have hθ24 : θ ∈ Icc (2 : ℝ) 4 := ⟨by linarith [hθ.1], hθ.2⟩
  have htwo : (2 : ℝ) ∈ Icc (2 : ℝ) 4 := by norm_num
  have hs0 : 0 ≤ su.1 := hsu.1
  have hsu' : su.1 ≤ su.2 := hsu.2.1
  have huT : su.2 ≤ T := hsu.2.2
  by_cases huS : su.2 ≤ S
  · rw [min_eq_left (hsu'.trans huS), min_eq_left huS]
    have heq := macroF_horizon_eq hT hS hST hI su ⟨hs0, hsu', huS⟩ θ
    have hd := integratedDominance hk hT hI hS hST le_rfl htwo
    norm_num at hd
    linarith
  · have hSu : S ≤ su.2 := (lt_of_not_ge huS).le
    rw [min_eq_right hSu]
    have hu0 := hs0.trans hsu'
    have hd2 := integratedDominance hk hT hI hu0 huT le_rfl htwo
    norm_num at hd2
    by_cases hsS : su.1 ≤ S
    · rw [min_eq_left hsS]
      have hp := psi_split hT hI hθ24 hs0 hsS hSu huT
      have ha := maxCost_split hT hI hS hSu huT le_rfl
      have hd := integratedDominance hk hT hI hS hSu huT hθ24
      have hn := maxCost_nonneg hk μ hSu
      have hθcost : 2 * integratedMaxCost μ S su.2 ≤ integratedPsi μ θ S su.2 := by
        exact (mul_le_mul_of_nonneg_right (by linarith [hθ.1] : 2 ≤ θ-1) hn).trans hd
      have hz : integratedPsi μ 2 S S = 0 := by simp [integratedPsi]
      simp only [macroF, hz]
      linarith
    · have hSs : S ≤ su.1 := (lt_of_not_ge hsS).le
      rw [min_eq_right hSs]
      have ha0 := maxCost_split hT hI (show (0 : ℝ) ≤ 0 by rfl) hS hSs (hsu'.trans huT)
      have ha1 := maxCost_split hT hI hS hSs hsu' huT
      have ha2 := maxCost_split hT hI hS hSu huT le_rfl
      have hd := integratedDominance hk hT hI hs0 hsu' huT hθ24
      have hn1 := maxCost_nonneg hk μ hSs
      have hn2 := maxCost_nonneg hk μ hsu'
      have hθcost : 2 * integratedMaxCost μ su.1 su.2 ≤ integratedPsi μ θ su.1 su.2 := by
        exact (mul_le_mul_of_nonneg_right (by linarith [hθ.1] : 2 ≤ θ-1) hn2).trans hd
      have hcoef : 2 * integratedMaxCost μ S su.1 ≤
          (θ + 3) / 2 * integratedMaxCost μ S su.1 :=
        mul_le_mul_of_nonneg_right (by linarith [hθ.1] : 2 ≤ (θ+3)/2) hn1
      have hzθ : integratedPsi μ θ S S = 0 := by simp [integratedPsi]
      have hz2 : integratedPsi μ 2 S S = 0 := by simp [integratedPsi]
      simp only [macroF, RiffleLowerV2.macroBeta, hzθ, hz2]
      rw [ha0]
      nlinarith

theorem lambda1_decay {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : RiffleLowerV2.ScalarIntegrable μ P T) :
    RiffleLowerV2.macroLambda1 μ T ≤
      RiffleLowerV2.macroLambda1 μ S - 2 * integratedMaxCost μ S T := by
  have hT := hS.trans hST
  have h := variational_le_of_lift (macroF μ T) (macroF μ S)
    (triangle T) (triangle S) (4 + 20 * (Real.log (k : ℝ) * T))
    (-2 * integratedMaxCost μ S T) (triangle_nonempty hT)
    (macroF_bound hk hT hT le_rfl hI) (macroF_bound hk hT hS hST hI) (by
      intro su hsu
      refine ⟨(min su.1 S, min su.2 S),
        ⟨le_min hsu.1 hS, min_le_min_right S hsu.2.1, min_le_right _ _⟩, ?_⟩
      intro θ hθ
      simpa only [sub_eq_add_neg, neg_mul] using macroF_clip_decay hk hS hST hI su hsu θ hθ)
  change RiffleLowerV2.macroLambda1 μ T ≤ RiffleLowerV2.macroLambda1 μ S +
    -2 * integratedMaxCost μ S T at h
  linarith

theorem beta_decay {k : ℕ} {μ : TimeLaw k} {P : BorelPartition k}
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) (hI : RiffleLowerV2.ScalarIntegrable μ P T) :
    RiffleLowerV2.macroBeta μ T = RiffleLowerV2.macroBeta μ S - integratedMaxCost μ S T := by
  have h := integratedMaxCost_add (hS.trans hST) hI hS hST le_rfl
  dsimp only [RiffleLowerV2.macroBeta]
  linarith

theorem reducedMargin_decay {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : RiffleLowerV2.ScalarIntegrable μ P T) :
    reducedMargin μ T ≤ reducedMargin μ S - integratedMaxCost μ S T := by
  have hb := beta_decay hS hST hI
  have hl := lambda1_decay hk hS hST hI
  have hn := maxCost_nonneg hk μ hST
  have hbS : RiffleLowerV2.macroBeta μ S ≤ reducedMargin μ S := le_max_left _ _
  have hlS : RiffleLowerV2.macroLambda1 μ S ≤ reducedMargin μ S := le_max_right _ _
  exact max_le (by linarith) (by linarith)

end RiffleMain.Critical
