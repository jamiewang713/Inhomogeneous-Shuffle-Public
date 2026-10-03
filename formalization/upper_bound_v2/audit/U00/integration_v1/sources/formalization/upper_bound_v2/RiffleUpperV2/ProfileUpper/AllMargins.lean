import RiffleUpperV2.ProfileUpper.Dominance

noncomputable section
open Set MeasureTheory
namespace RiffleUpperV2.ProfileUpper
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

theorem expression_bound2 {a x y z C : ℝ}
    (ha : a ∈ Icc (3 : ℝ) 4) (hC : 0 ≤ C)
    (hx : 0 ≤ x ∧ x ≤ C) (hy : 0 ≤ y ∧ y ≤ 4*C)
    (hz : 0 ≤ z ∧ z ≤ 4*C) :
    |(a-1)/2*(1-x)-y-2*z| ≤ 4+20*C := by
  have hc0 : 0 ≤ (a-1)/2 := by linarith [ha.1]
  have hc : (a-1)/2 ≤ 3/2 := by linarith [ha.2]
  have hprod0 := mul_nonneg hc0 hx.1
  have hprod : (a-1)/2*x ≤ (3/2)*C := mul_le_mul hc hx.2 hx.1 (by norm_num)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem macroF2_bound {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T H : ℝ} (hT : 0 ≤ T) (_hH : 0 ≤ H) (hHT : H ≤ T)
    (hI : ScalarIntegrable μ P T) (su : ℝ × ℝ) (hsu : su ∈ triangle H)
    (a : ℝ) (ha : a ∈ Icc (3 : ℝ) 4) :
    |macroF2 μ H a su.1 su.2| ≤ 4+20*(Real.log (k : ℝ)*T) := by
  have hl : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have ha24 : a ∈ Icc (2 : ℝ) 4 := ⟨by linarith [ha.1], ha.2⟩
  have hs : 0 ≤ su.1 := hsu.1
  have hsu' : su.1 ≤ su.2 := hsu.2.1
  have hu : su.2 ≤ H := hsu.2.2
  have hA := scalar_bounds hT hI.2.1 (profileMaxCost_bounds hk μ) (by rfl) hs
    ((hsu'.trans hu).trans hHT)
  have hB := scalar_bounds hT (hI.2.2 a ha24)
    (fun t => profilePsi_bounds hk μ t ha24) hs hsu' (hu.trans hHT)
  have hB2 := scalar_bounds hT (hI.2.2 2 (by norm_num))
    (fun t => profilePsi_bounds hk μ t (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num))
    (hs.trans hsu') hu hHT
  have hA' : integratedMaxCost μ 0 su.1 ≤ Real.log (k : ℝ)*T := by
    dsimp [integratedMaxCost]
    nlinarith [mul_le_mul_of_nonneg_left ((hsu'.trans hu).trans hHT) hl]
  have hB' : integratedPsi μ a su.1 su.2 ≤ 4*(Real.log (k : ℝ)*T) := by
    dsimp [integratedPsi]
    nlinarith [mul_nonneg hl hs]
  have hB2' : integratedPsi μ 2 su.2 H ≤ 4*(Real.log (k : ℝ)*T) := by
    dsimp [integratedPsi]
    nlinarith [mul_nonneg hl (hs.trans hsu'), mul_le_mul_of_nonneg_left hHT hl]
  exact expression_bound2 ha (mul_nonneg hl hT) ⟨hA.1, hA'⟩ ⟨hB.1, hB'⟩ ⟨hB2.1, hB2'⟩

theorem macroF2_clip_le {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : ScalarIntegrable μ P T) (su : ℝ × ℝ) (hsu : su ∈ triangle T)
    (a : ℝ) (ha : a ∈ Icc (3 : ℝ) 4) :
    macroF2 μ T a su.1 su.2 ≤ macroF2 μ S a (min su.1 S) (min su.2 S) := by
  have ha24 : a ∈ Icc (2 : ℝ) 4 := ⟨by linarith [ha.1], ha.2⟩
  have hA := scalar_clip_le hT hI.2.1 (fun t => (profileMaxCost_bounds hk μ t).1)
    hS hST (le_refl 0) hsu.1 (hsu.2.1.trans hsu.2.2)
  rw [min_eq_left hS] at hA
  have hB := scalar_clip_le hT (hI.2.2 a ha24)
    (fun t => (profilePsi_bounds hk μ t ha24).1) hS hST hsu.1 hsu.2.1 hsu.2.2
  have hB2 := scalar_clip_le hT (hI.2.2 2 (by norm_num))
    (fun t => (profilePsi_bounds hk μ t (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num)).1)
    hS hST (hsu.1.trans hsu.2.1) hsu.2.2 le_rfl
  rw [min_eq_right hST] at hB2
  have hmul := mul_le_mul_of_nonneg_left hA (show 0 ≤ (a-1)/2 by linarith [ha.1])
  dsimp [macroF2, macroBeta, RiffleLowerV2.macroBeta, integratedMaxCost, integratedPsi]
  linarith

theorem lambda2Monotonicity {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : ScalarIntegrable μ P T) : macroLambda2 μ T ≤ macroLambda2 μ S := by
  have hT := hS.trans hST
  have hh := variational_le_of_lift (macroF2 μ T) (macroF2 μ S)
    (triangle T) (triangle S) (4+20*(Real.log (k:ℝ)*T)) 0 (triangle_nonempty hT)
    (macroF2_bound hk hT hT le_rfl hI) (macroF2_bound hk hT hS hST hI) (by
      intro su hsu
      refine ⟨(min su.1 S, min su.2 S),
        ⟨le_min hsu.1 hS, min_le_min_right S hsu.2.1, min_le_right _ _⟩, ?_⟩
      intro a ha
      simpa only [add_zero] using macroF2_clip_le hk hT hS hST hI su hsu a ha)
  simpa only [add_zero, macroLambda2] using hh

theorem scalarIntegrable_restrict {k : ℕ} {μ : TimeLaw k} {P : BorelPartition k}
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) (hI : ScalarIntegrable μ P T) :
    ScalarIntegrable μ P S := by
  refine ⟨fun i => scalar_restrict (hS.trans hST) (hI.1 i) le_rfl hS hST,
    scalar_restrict (hS.trans hST) hI.2.1 le_rfl hS hST, ?_⟩
  intro a ha
  exact scalar_restrict (hS.trans hST) (hI.2.2 a ha) le_rfl hS hST

theorem betaMonotonicity {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : ScalarIntegrable μ P T) : macroBeta μ T ≤ macroBeta μ S := by
  have hh := scalar_mono (hS.trans hST) hI.2.1 (fun t => (profileMaxCost_bounds hk μ t).1)
    (le_refl 0) (le_refl 0) hS hST le_rfl
  dsimp [macroBeta, RiffleLowerV2.macroBeta, integratedMaxCost]
  linarith

theorem lambda3_eq_beta {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T : ℝ} (hT : 0 ≤ T) (hI : ScalarIntegrable μ P T) :
    macroLambda3 μ T = macroBeta μ T := by
  refine le_antisymm (lambda3_le_beta hk hT hI) ?_
  have hb : BddAbove ((fun s => macroBeta μ s - integratedPsi μ 2 s T) '' Icc 0 T) := by
    refine ⟨macroBeta μ T, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hd := integratedDominance hk hT hI hs.1 hs.2 le_rfl (show (2:ℝ) ∈ Icc 2 4 by norm_num)
    have ha := integratedMaxCost_add hT hI hs.1 hs.2 le_rfl
    dsimp [macroBeta, RiffleLowerV2.macroBeta]
    linarith
  have hh := le_csSup hb (show macroBeta μ T - integratedPsi μ 2 T T ∈
    (fun s => macroBeta μ s - integratedPsi μ 2 s T) '' Icc 0 T from ⟨T, ⟨hT,le_rfl⟩,rfl⟩)
  simpa only [macroLambda3, integratedPsi, intervalIntegral.integral_same, sub_zero] using hh

theorem allMarginMonotonicity {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : ScalarIntegrable μ P T) :
    macroBeta μ T ≤ macroBeta μ S ∧ macroLambda1 μ T ≤ macroLambda1 μ S ∧
    macroLambda2 μ T ≤ macroLambda2 μ S ∧ macroLambda3 μ T ≤ macroLambda3 μ S ∧
    fullMargin μ T ≤ fullMargin μ S := by
  have hIS := scalarIntegrable_restrict hS hST hI
  refine ⟨betaMonotonicity hk hS hST hI, ?_, lambda2Monotonicity hk hS hST hI, ?_, ?_⟩
  · have hh := (macroLambda_horizon hk (hS.trans hST) hS hST hI).1
    linarith
  · rw [lambda3_eq_beta hk (hS.trans hST) hI, lambda3_eq_beta hk hS hIS]
    exact betaMonotonicity hk hS hST hI
  · rw [dominanceReduction hk (hS.trans hST) hI, dominanceReduction hk hS hIS]
    exact marginMonotonicity hk hS hST hI

end RiffleUpperV2.ProfileUpper
