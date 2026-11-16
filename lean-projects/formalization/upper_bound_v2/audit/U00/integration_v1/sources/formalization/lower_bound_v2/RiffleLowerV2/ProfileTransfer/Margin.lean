import RiffleLowerV2.ProfileTransfer.Empirical
import RiffleLowerV2.ProfileTransfer.Spatial
import RiffleLowerV2.ProfileTransfer.Extrema

noncomputable section
open Set MeasureTheory
namespace RiffleLowerV2.ProfileTransfer
open TimeProfile

private theorem scalar_restrict {f : ℝ → ℝ} {T a b : ℝ}
    (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IntervalIntegrable f volume a b := by
  apply hf.mono_set
  rw [uIcc_of_le hab, uIcc_of_le hT]
  exact Icc_subset_Icc ha hb

private theorem scalar_bounds {f : ℝ → ℝ} {T a b M : ℝ}
    (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T)
    (hbound : ∀ t, 0 ≤ f t ∧ f t ≤ M)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    0 ≤ (∫ t in a..b, f t) ∧ (∫ t in a..b, f t) ≤ M*(b-a) := by
  refine ⟨intervalIntegral.integral_nonneg_of_forall hab (fun t => (hbound t).1), ?_⟩
  have h := intervalIntegral.integral_mono_on hab (scalar_restrict hT hf ha hab hb)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume a b)
    (fun t _ => (hbound t).2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

private theorem scalar_mono {f : ℝ → ℝ} {T a b c d : ℝ}
    (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T)
    (hpos : ∀ t, 0 ≤ f t) (hc : 0 ≤ c) (hca : c ≤ a)
    (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ T) :
    (∫ t in a..b, f t) ≤ ∫ t in c..d, f t :=
  intervalIntegral.integral_mono_interval hca hab hbd
    (ae_of_all _ hpos) (scalar_restrict hT hf hc (hca.trans (hab.trans hbd)) hd)

private theorem expression_bound {a x y z C : ℝ}
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

private theorem macroF_bound {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
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

private theorem empiricalF_bound {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) {T : ℝ} (hT : 0 ≤ T) (hKT : horizon N K ≤ T)
    (su : ℝ × ℝ) (hsu : su ∈ triangle (horizon N K))
    (a : ℝ) (ha : a ∈ Icc (3 : ℝ) 4) :
    |F cuts (Targets.deckPos hN) a su.1 su.2| ≤ 4+20*(Real.log (k : ℝ)*T) := by
  have hl : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have ha24 : a ∈ Icc (2 : ℝ) 4 := ⟨by linarith [ha.1], ha.2⟩
  have hs : 0 ≤ su.1 := hsu.1
  have hsu' : su.1 ≤ su.2 := hsu.2.1
  have hu : su.2 ≤ horizon N K := hsu.2.2
  have hA0 := empiricalIntegral_nonneg hN
    (fun j => (TimeProfile.maxCost_bounds hk (cuts.profile (Targets.deckPos hN) j)).1) hs
  have hA := empiricalIntegral_le hN
    (fun j => (TimeProfile.maxCost_bounds hk (cuts.profile (Targets.deckPos hN) j)).2)
    (le_refl 0) hs (hsu'.trans hu)
  have hB0 := empiricalIntegral_nonneg hN
    (fun j => (TimeProfile.psi_bounds hk (cuts.profile (Targets.deckPos hN) j) ha24).1) hsu'
  have hB := empiricalIntegral_le hN
    (fun j => (TimeProfile.psi_bounds hk (cuts.profile (Targets.deckPos hN) j) ha24).2)
    hs hsu' hu
  have hB20 := empiricalIntegral_nonneg hN
    (fun j => (TimeProfile.psi_bounds hk (cuts.profile (Targets.deckPos hN) j)
      (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num)).1) hu
  have hB2 := empiricalIntegral_le hN
    (fun j => (TimeProfile.psi_bounds hk (cuts.profile (Targets.deckPos hN) j)
      (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num)).2)
    (hs.trans hsu') hu le_rfl
  apply expression_bound ha (mul_nonneg hl hT)
  · exact ⟨hA0, by dsimp [A]; nlinarith [mul_le_mul_of_nonneg_left ((hsu'.trans hu).trans hKT) hl]⟩
  · exact ⟨hB0, by dsimp [B]; nlinarith [mul_nonneg hl hs, mul_le_mul_of_nonneg_left (hu.trans hKT) hl]⟩
  · exact ⟨hB20, by dsimp [B]; nlinarith [mul_nonneg hl (hs.trans hsu'), mul_le_mul_of_nonneg_left hKT hl]⟩

private theorem common_F_error {k N : ℕ} {T e : ℝ} (hN : 2 ≤ N)
    (cuts : Targets.HorizonCuts k N T) (μ : TimeLaw k)
    (he : 0 ≤ e) (herr : Targets.ProfileIntervalErrors T cuts (Targets.deckPos hN) μ e)
    (su : ℝ × ℝ) (hsu : su ∈ triangle (horizon N (horizonDepth N T)))
    (a : ℝ) (ha : a ∈ Icc (3 : ℝ) 4) :
    |F cuts (Targets.deckPos hN) a su.1 su.2 -
      macroF μ (horizon N (horizonDepth N T)) a su.1 su.2| ≤ (13/2 : ℝ)*e := by
  have hA := herr.1 0 su.1 le_rfl hsu.1 (hsu.2.1.trans hsu.2.2)
  have hB := herr.2 a ⟨by linarith [ha.1], ha.2⟩ su.1 su.2 hsu.1 hsu.2.1 hsu.2.2
  have hB2 := herr.2 2 (by norm_num) su.2 (horizon N (horizonDepth N T))
    (hsu.1.trans hsu.2.1) hsu.2.2 le_rfl
  have hc : 0 ≤ (a+3)/2 ∧ (a+3)/2 ≤ 7/2 := by constructor <;> linarith [ha.1, ha.2]
  have hA' := mul_le_mul_of_nonneg_left (abs_le.mp hA).1 hc.1
  have hA'' := mul_le_mul_of_nonneg_left (abs_le.mp hA).2 hc.1
  have hce := mul_le_mul_of_nonneg_right hc.2 he
  apply abs_le.mpr
  dsimp [F, beta, macroF, macroBeta]
  constructor <;> nlinarith [(abs_le.mp hB).1, (abs_le.mp hB).2,
    (abs_le.mp hB2).1, (abs_le.mp hB2).2]

/-- Clipping removes a terminal portion of a nonnegative scalar integral. -/
private theorem scalar_clip_le {f : ℝ → ℝ} {T S a b : ℝ}
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

private theorem macroF_clip_le {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
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
  dsimp [macroF, macroBeta, integratedMaxCost, integratedPsi]
  linarith

private theorem macroF_horizon_eq {k : ℕ} {μ : TimeLaw k}
    {P : BorelPartition k} {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hST : S ≤ T)
    (hI : ScalarIntegrable μ P T) (su : ℝ × ℝ) (hsu : su ∈ triangle S) (a : ℝ) :
    macroF μ S a su.1 su.2 = macroF μ T a su.1 su.2 + 2*integratedPsi μ 2 S T := by
  have hI2 := hI.2.2 2 (show (2 : ℝ) ∈ Icc (2 : ℝ) 4 by norm_num)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (scalar_restrict hT hI2 (hsu.1.trans hsu.2.1) hsu.2.2 hST)
    (scalar_restrict hT hI2 hS hST le_rfl)
  dsimp [macroF, integratedPsi]
  linarith

private theorem triangle_nonempty {S : ℝ} (hS : 0 ≤ S) : (triangle S).Nonempty :=
  ⟨(0,0), le_rfl, le_rfl, hS⟩

private theorem macroLambda_horizon {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
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

private theorem common_lambda_error {k N : ℕ} (hk : 2 ≤ k) {T e : ℝ}
    (hN : 2 ≤ N) (hT : 0 ≤ T) (cuts : Targets.HorizonCuts k N T)
    (P : BorelPartition k) (μ : TimeLaw k) (hI : ScalarIntegrable μ P T)
    (he : 0 ≤ e) (herr : Targets.ProfileIntervalErrors T cuts (Targets.deckPos hN) μ e) :
    |lambda1 cuts (Targets.deckPos hN) - macroLambda1 μ (horizon N (horizonDepth N T))| ≤
      (13/2 : ℝ)*e := by
  let S := horizon N (horizonDepth N T)
  let C := 4+20*(Real.log (k : ℝ)*T)
  have hL := logScale_pos hN
  have hS : 0 ≤ S := by dsimp [S, horizon]; positivity
  have hST : S ≤ T := by
    have h := (horizonDepth_error hN hT).1
    dsimp [S, horizon]
    linarith
  have hb := empiricalF_bound hk hN cuts hT hST
  have hbμ := macroF_bound hk hT hS hST hI
  have hfg := common_F_error hN cuts μ he herr
  have h1 := variational_le_of_lift (F cuts (Targets.deckPos hN)) (macroF μ S)
    (triangle S) (triangle S) C ((13/2 : ℝ)*e) (triangle_nonempty hS) hb hbμ (by
      intro su hsu
      refine ⟨su, hsu, ?_⟩
      intro a ha
      have h := (abs_le.mp (hfg su hsu a ha)).2
      linarith)
  have h2 := variational_le_of_lift (macroF μ S) (F cuts (Targets.deckPos hN))
    (triangle S) (triangle S) C ((13/2 : ℝ)*e) (triangle_nonempty hS) hbμ hb (by
      intro su hsu
      refine ⟨su, hsu, ?_⟩
      intro a ha
      have h := (abs_le.mp (hfg su hsu a ha)).1
      linarith)
  change lambda1 cuts (Targets.deckPos hN) ≤ macroLambda1 μ S + (13/2 : ℝ)*e at h1
  change macroLambda1 μ S ≤ lambda1 cuts (Targets.deckPos hN) + (13/2 : ℝ)*e at h2
  apply abs_le.mpr
  constructor <;> linarith

/-- The source margin transfer, under exactly the selected partition's scalar predicate. -/
theorem marginTransfer : Targets.MarginTransferTarget := by
  intro k N hk hN T hT P μ hI cuts e he herr
  let S := horizon N (horizonDepth N T)
  let Lk := Real.log (k : ℝ)
  have hLk : 0 ≤ Lk := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hL := logScale_pos hN
  have hS : 0 ≤ S := by dsimp [S, horizon]; positivity
  have hround := horizonDepth_error hN hT.le
  have hST : S ≤ T := by dsimp [S, horizon]; linarith [hround.1]
  have hgap : T-S ≤ 1/logScale N := by exact hround.2.le
  have hterm : Lk*(T-S) ≤ Lk/logScale N := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hgap hLk
  constructor
  · have hA := herr.1 0 S le_rfl hS le_rfl
    have htail := scalar_bounds hT.le hI.2.1 (profileMaxCost_bounds hk μ) hS hST le_rfl
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (scalar_restrict hT.le hI.2.1 (le_refl 0) hS hST)
      (scalar_restrict hT.le hI.2.1 hS hST le_rfl)
    change integratedMaxCost μ 0 S + integratedMaxCost μ S T = integratedMaxCost μ 0 T at hsplit
    change 0 ≤ integratedMaxCost μ S T ∧ integratedMaxCost μ S T ≤ Lk*(T-S) at htail
    apply abs_le.mpr
    dsimp [beta, macroBeta]
    constructor <;> linarith [(abs_le.mp hA).1, (abs_le.mp hA).2]
  · have heCommon := common_lambda_error hk hN hT.le cuts P μ hI he herr
    have heHorizon := macroLambda_horizon hk hT.le hS hST hI
    change |lambda1 cuts (Targets.deckPos hN) - macroLambda1 μ S| ≤ (13/2 : ℝ)*e at heCommon
    have heTerminal : |macroLambda1 μ S-macroLambda1 μ T| ≤ 8*Lk/logScale N := by
      rw [abs_of_nonneg heHorizon.1]
      calc
        _ ≤ 8*Lk*(T-S) := heHorizon.2
        _ = 8*(Lk*(T-S)) := by ring
        _ ≤ 8*(Lk/logScale N) := mul_le_mul_of_nonneg_left hterm (by norm_num)
        _ = _ := by ring
    calc
      _ ≤ |lambda1 cuts (Targets.deckPos hN)-macroLambda1 μ S| +
          |macroLambda1 μ S-macroLambda1 μ T| := abs_sub_le _ _ _
      _ ≤ (13/2 : ℝ)*e+8*Lk/logScale N := add_le_add heCommon heTerminal
      _ ≤ (13/2 : ℝ)*e+14*Real.log (k : ℝ)/logScale N := by
        exact add_le_add le_rfl
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (show (8 : ℝ) ≤ 14 by norm_num) hLk) hL.le)

end RiffleLowerV2.ProfileTransfer
