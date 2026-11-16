import RiffleUpperV2.ProfileUpper.Analytic

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RiffleUpperV2.ProfileUpper
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

theorem basicOneColumn {k : ℕ} (p : Simplex k) {θ : ℝ} (hθ : 1 ≤ θ) :
    (θ-1) * maxCost p ≤ psi p θ := by
  have hp : powerSum p θ ≤ pileMax p ^ (θ-1) := by
    calc
      _ = ∑ d, (prob p d)^(θ-1) * prob p d := by
        apply Finset.sum_congr rfl
        intro d _
        have hh := Real.rpow_add_one' (prob_nonneg p d) (show θ-1+1 ≠ 0 by linarith)
        simpa using hh
      _ ≤ ∑ d, pileMax p^(θ-1) * prob p d := by
        apply Finset.sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (prob_nonneg p d) (prob_le_pileMax p d) (by linarith))
          (prob_nonneg p d)
      _ = pileMax p^(θ-1) := by rw [← Finset.mul_sum, sum_prob, mul_one]
  have hh := Real.log_le_log (powerSum_pos p hθ) hp
  rw [Real.log_rpow (pileMax_pos p)] at hh
  simp only [maxCost, digitCost, one_div, Real.log_inv, psi]
  nlinarith

theorem profileDominance {k : ℕ} (hk : 2 ≤ k) (μ : TimeLaw k) (t : ℝ)
    {θ : ℝ} (hθ : θ ∈ Icc (2 : ℝ) 4) :
    (θ-1) * profileMaxCost μ t ≤ profilePsi μ t θ := by
  have h := integral_mono ((integrable_maxCost hk (μ t)).const_mul (θ-1))
    (integrable_psi hk (μ t) hθ) (fun p => basicOneColumn p (by linarith [hθ.1]))
  simpa only [integral_const_mul, profileMaxCost, profilePsi] using h

theorem integratedDominance {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T r s θ : ℝ} (hT : 0 ≤ T)
    (hI : ScalarIntegrable μ P T) (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ T)
    (hθ : θ ∈ Icc (2 : ℝ) 4) :
    (θ-1)*integratedMaxCost μ r s ≤ integratedPsi μ θ r s := by
  have h := intervalIntegral.integral_mono_on hrs
    ((scalar_restrict hT hI.2.1 hr hrs hs).const_mul (θ-1))
    (scalar_restrict hT (hI.2.2 θ hθ) hr hrs hs)
    (fun t _ => profileDominance hk μ t hθ)
  simpa only [intervalIntegral.integral_const_mul, integratedMaxCost, integratedPsi] using h

def macroF2 {k : ℕ} (μ : TimeLaw k) (T θ s u : ℝ) : ℝ :=
  (θ-1)/2 * macroBeta μ s - integratedPsi μ θ s u - 2*integratedPsi μ 2 u T

def macroLambda2 {k : ℕ} (μ : TimeLaw k) (T : ℝ) : ℝ :=
  sSup ((fun su : ℝ × ℝ => sInf ((fun θ => macroF2 μ T θ su.1 su.2) '' Icc 3 4)) '' triangle T)

def macroLambda3 {k : ℕ} (μ : TimeLaw k) (T : ℝ) : ℝ :=
  sSup ((fun s => macroBeta μ s - integratedPsi μ 2 s T) '' Icc 0 T)

def fullMargin {k : ℕ} (μ : TimeLaw k) (T : ℝ) : ℝ :=
  max (max (macroBeta μ T) (macroLambda1 μ T)) (max (macroLambda2 μ T) (macroLambda3 μ T))

def fullCriticalTime {k : ℕ} (μ : TimeLaw k) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {T : ℝ | 0 < T ∧ fullMargin μ T < 0})

theorem integratedMaxCost_add {k : ℕ} {μ : TimeLaw k} {P : BorelPartition k}
    {T s u : ℝ} (hT : 0 ≤ T) (hI : ScalarIntegrable μ P T)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u ≤ T) :
    integratedMaxCost μ 0 u = integratedMaxCost μ 0 s + integratedMaxCost μ s u := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (scalar_restrict hT hI.2.1 (le_refl 0) hs (hsu.trans hu))
    (scalar_restrict hT hI.2.1 hs hsu hu)).symm

theorem lambda3_le_beta {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T : ℝ} (hT : 0 ≤ T) (hI : ScalarIntegrable μ P T) :
    macroLambda3 μ T ≤ macroBeta μ T := by
  apply csSup_le ((nonempty_Icc.mpr hT).image _)
  rintro _ ⟨s, hs, rfl⟩
  have hd := integratedDominance hk hT hI hs.1 hs.2 le_rfl (show (2:ℝ) ∈ Icc 2 4 by norm_num)
  have ha := integratedMaxCost_add hT hI hs.1 hs.2 le_rfl
  dsimp [macroBeta, RiffleLowerV2.macroBeta]
  linarith

theorem lambda2_le_beta {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T : ℝ} (hT : 0 ≤ T) (hI : ScalarIntegrable μ P T) :
    macroLambda2 μ T ≤ macroBeta μ T := by
  apply csSup_le ((triangle_nonempty hT).image _)
  rintro _ ⟨su, hs, rfl⟩
  have hb : BddBelow ((fun θ => macroF2 μ T θ su.1 su.2) '' Icc (3:ℝ) 4) := by
    refine ⟨-(4+20*(Real.log (k:ℝ)*T))-2*macroBeta μ su.1, ?_⟩
    rintro _ ⟨θ, hθ, rfl⟩
    have hh := (abs_le.mp (macroF_bound hk hT hT le_rfl hI su hs θ hθ)).1
    dsimp [macroF, macroF2] at hh ⊢
    nlinarith
  have hi := csInf_le hb (show macroF2 μ T 3 su.1 su.2 ∈
    (fun θ => macroF2 μ T θ su.1 su.2) '' Icc (3:ℝ) 4 from ⟨3, by norm_num, rfl⟩)
  have hd3 := integratedDominance hk hT hI hs.1 hs.2.1 hs.2.2
    (show (3:ℝ) ∈ Icc 2 4 by norm_num)
  have hd2 := integratedDominance hk hT hI (hs.1.trans hs.2.1) hs.2.2 le_rfl
    (show (2:ℝ) ∈ Icc 2 4 by norm_num)
  have hA0 := intervalIntegral.integral_nonneg_of_forall (μ := volume) hs.2.1
    (fun t => (profileMaxCost_bounds hk μ t).1)
  have hA1 := intervalIntegral.integral_nonneg_of_forall (μ := volume) hs.2.2
    (fun t => (profileMaxCost_bounds hk μ t).1)
  change 0 ≤ integratedMaxCost μ su.1 su.2 at hA0
  change 0 ≤ integratedMaxCost μ su.2 T at hA1
  have ha := integratedMaxCost_add hT hI hs.1 hs.2.1 hs.2.2
  have hb := integratedMaxCost_add hT hI (hs.1.trans hs.2.1) hs.2.2 le_rfl
  dsimp [macroF2, macroBeta, RiffleLowerV2.macroBeta] at hi ⊢
  linarith

theorem dominanceReduction {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    {P : BorelPartition k} {T : ℝ} (hT : 0 ≤ T) (hI : ScalarIntegrable μ P T) :
    fullMargin μ T = reducedMargin μ T := by
  have h2 := lambda2_le_beta hk hT hI
  have h3 := lambda3_le_beta hk hT hI
  exact max_eq_left (max_le (h2.trans (le_max_left _ _)) (h3.trans (le_max_left _ _)))

theorem criticalTime_eq_full {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hI : ∀ T : ℝ, 0 < T → ∃ P : BorelPartition k, ScalarIntegrable μ P T) :
    criticalTime μ = fullCriticalTime μ := by
  unfold criticalTime fullCriticalTime
  congr 2
  ext T
  by_cases hT : 0 < T
  · obtain ⟨P, hP⟩ := hI T hT
    simp only [mem_setOf_eq, hT, true_and, dominanceReduction hk hT.le hP]
  · simp [hT]

end RiffleUpperV2.ProfileUpper
