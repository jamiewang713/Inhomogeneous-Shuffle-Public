import RiffleUpperV2.Shared.Profile
import RiffleLowerV2.ProfileTransfer.Extrema
import RiffleLowerV2.ProfileTransfer.Spatial

noncomputable section
open Set MeasureTheory
namespace RiffleUpperV2.ProfileUpper
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

theorem scalar_restrict {f : ℝ → ℝ} {T a b : ℝ}
    (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IntervalIntegrable f volume a b := by
  apply hf.mono_set
  rw [uIcc_of_le hab, uIcc_of_le hT]
  exact Icc_subset_Icc ha hb

theorem scalar_bounds {f : ℝ → ℝ} {T a b M : ℝ}
    (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T)
    (hbound : ∀ t, 0 ≤ f t ∧ f t ≤ M)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    0 ≤ (∫ t in a..b, f t) ∧ (∫ t in a..b, f t) ≤ M*(b-a) := by
  refine ⟨intervalIntegral.integral_nonneg_of_forall hab (fun t => (hbound t).1), ?_⟩
  have h := intervalIntegral.integral_mono_on hab (scalar_restrict hT hf ha hab hb)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume a b)
    (fun t _ => (hbound t).2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

theorem scalar_mono {f : ℝ → ℝ} {T a b c d : ℝ}
    (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T)
    (hpos : ∀ t, 0 ≤ f t) (hc : 0 ≤ c) (hca : c ≤ a)
    (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ T) :
    (∫ t in a..b, f t) ≤ ∫ t in c..d, f t :=
  intervalIntegral.integral_mono_interval hca hab hbd
    (ae_of_all _ hpos) (scalar_restrict hT hf hc (hca.trans (hab.trans hbd)) hd)

theorem expression_bound {a x y z C : ℝ}
    (ha : a ∈ Icc (3 : ℝ) 4) (hC : 0 ≤ C)
    (hx : 0 ≤ x ∧ x ≤ C) (hy : 0 ≤ y ∧ y ≤ 4*C)
    (hz : 0 ≤ z ∧ z ≤ 4*C) :
    |(a+3)/2*(1-x)-y-2*z| ≤ 4+20*C := by
  have hc0 : 0 ≤ (a+3)/2 := by linarith [ha.1]
  have hc : (a+3)/2 ≤ 7/2 := by linarith [ha.2]
  have hprod0 := mul_nonneg hc0 hx.1
  have hprod : (a+3)/2*x ≤ (7/2)*C := mul_le_mul hc hx.2 hx.1 (by norm_num)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem macroF_bound {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T H : ℝ} (hT : 0 ≤ T) (_hH : 0 ≤ H) (hHT : H ≤ T)
    (hI : ScalarIntegrable μ P T) (su : ℝ × ℝ) (hsu : su ∈ triangle H)
    (a : ℝ) (ha : a ∈ Icc (3 : ℝ) 4) :
    |macroF μ H a su.1 su.2| ≤ 4+20*(Real.log (k : ℝ)*T) := by
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
  exact expression_bound ha (mul_nonneg hl hT) ⟨hA.1, hA'⟩ ⟨hB.1, hB'⟩ ⟨hB2.1, hB2'⟩

theorem scalar_clip_le {f : ℝ → ℝ} {T S a b : ℝ}
    (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T)
    (hpos : ∀ t, 0 ≤ f t) (_hS : 0 ≤ S) (_hST : S ≤ T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ t in min a S..min b S, f t) ≤ ∫ t in a..b, f t := by
  by_cases haS : a ≤ S
  · rw [min_eq_left haS]
    exact scalar_mono hT hf hpos ha le_rfl (le_min hab haS) (min_le_left _ _) hb
  · have hSa : S ≤ a := (not_le.mp haS).le
    rw [min_eq_right hSa, min_eq_right (hSa.trans hab), intervalIntegral.integral_same]
    exact intervalIntegral.integral_nonneg_of_forall hab hpos

theorem macroF_clip_le {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : ScalarIntegrable μ P T) (su : ℝ × ℝ) (hsu : su ∈ triangle T)
    (a : ℝ) (ha : a ∈ Icc (3 : ℝ) 4) :
    macroF μ T a su.1 su.2 ≤ macroF μ S a (min su.1 S) (min su.2 S) := by
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
  have hmul := mul_le_mul_of_nonneg_left hA (show 0 ≤ (a+3)/2 by linarith [ha.1])
  dsimp [macroF, RiffleLowerV2.macroBeta, integratedMaxCost, integratedPsi]
  linarith

theorem macroF_horizon_eq {k : ℕ} {μ : TimeLaw k}
    {P : BorelPartition k} {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : ScalarIntegrable μ P T) (su : ℝ × ℝ) (hsu : su ∈ triangle S) (a : ℝ) :
    macroF μ S a su.1 su.2 = macroF μ T a su.1 su.2 + 2*integratedPsi μ 2 S T := by
  have hI2 := hI.2.2 2 (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (scalar_restrict hT hI2 (hsu.1.trans hsu.2.1) hsu.2.2 hST)
    (scalar_restrict hT hI2 hS hST le_rfl)
  dsimp [macroF, integratedPsi]
  linarith

theorem triangle_nonempty {S : ℝ} (hS : 0 ≤ S) : (triangle S).Nonempty :=
  ⟨(0,0), le_rfl, le_rfl, hS⟩

theorem macroLambda_horizon {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : ScalarIntegrable μ P T) :
    0 ≤ macroLambda1 μ S - macroLambda1 μ T ∧
      macroLambda1 μ S - macroLambda1 μ T ≤ 8*Real.log (k : ℝ)*(T-S) := by
  let C := 4+20*(Real.log (k : ℝ)*T)
  have hbS := macroF_bound hk hT hS hST hI
  have hbT := macroF_bound hk hT hT le_rfl hI
  have hlo := variational_le_of_lift (macroF μ T) (macroF μ S)
    (triangle T) (triangle S) C 0 (triangle_nonempty hT) hbT hbS (by
      intro su hsu
      refine ⟨(min su.1 S, min su.2 S), ?_, ?_⟩
      · exact ⟨le_min hsu.1 hS, min_le_min_right S hsu.2.1, min_le_right _ _⟩
      · intro a ha
        simpa only [add_zero] using macroF_clip_le hk hT hS hST hI su hsu a ha)
  have hhi := variational_le_of_lift (macroF μ S) (macroF μ T)
    (triangle S) (triangle T) C (2*integratedPsi μ 2 S T)
    (triangle_nonempty hS) hbS hbT (by
      intro su hsu
      refine ⟨su, ⟨hsu.1, hsu.2.1, hsu.2.2.trans hST⟩, ?_⟩
      intro a _
      exact (macroF_horizon_eq hT hS hST hI su hsu a).le)
  change macroLambda1 μ T ≤ macroLambda1 μ S + 0 at hlo
  change macroLambda1 μ S ≤ macroLambda1 μ T + 2*integratedPsi μ 2 S T at hhi
  have htail := scalar_bounds hT (hI.2.2 2 (by norm_num))
    (fun t => profilePsi_bounds hk μ t (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num))
    hS hST le_rfl
  change 0 ≤ integratedPsi μ 2 S T ∧ integratedPsi μ 2 S T ≤ _ at htail
  constructor <;> linarith

theorem marginMonotonicity {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : ScalarIntegrable μ P T) : reducedMargin μ T ≤ reducedMargin μ S := by
  have hT := hS.trans hST
  have hA := scalar_mono hT hI.2.1 (fun t => (profileMaxCost_bounds hk μ t).1)
    (le_refl 0) (le_refl 0) hS hST le_rfl
  have hB : RiffleLowerV2.macroBeta μ T ≤ RiffleLowerV2.macroBeta μ S := by
    dsimp [RiffleLowerV2.macroBeta, integratedMaxCost]
    linarith
  have hL := (macroLambda_horizon hk hT hS hST hI).1
  exact max_le_max hB (by linarith)

end RiffleUpperV2.ProfileUpper
