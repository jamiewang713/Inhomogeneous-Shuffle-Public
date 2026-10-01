import RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature
import Contracts.v1.TransferFinite
import RiffleLowerV2.ProfileTransfer.Endpoint

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RiffleLowerV2.ProfileTransfer
open TimeProfile

/-- The complementary observable converts the historical lower estimate into both directions. -/
theorem sampledQuadrature {k N : ℕ} (hN : 2 ≤ N) {T rho phi omega M : ℝ}
    (hT : 0 < T) (hrho : 0 < rho) (hphi : 0 ≤ phi) (homega : 0 ≤ omega) (hM : 0 ≤ M)
    (P : BorelPartition k) (μ : TimeLaw k) (f : Simplex k → ℝ)
    (hcont : Continuous f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M)
    (hosc : ∀ i p q, P.classify p = i → P.classify q = i → |f p - f q| ≤ omega)
    (htime : IntervalIntegrable (fun t => ∫ p, f p ∂(μ t : Measure (Simplex k))) volume 0 T)
    (cuts : Targets.HorizonCuts k N T)
    (hLike : AlmostLike cuts (Targets.deckPos hN) μ P T rho phi)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ T) :
    |(∑ j ∈ Compat.timePositions N (horizonDepth N T) r s,
      f (cuts.profile (Targets.deckPos hN) j)) / logScale N -
        ∫ t in r..s, ∫ p, f p ∂(μ t : Measure (Simplex k))| ≤
      Compat.quadratureError N T rho phi P.cellCount M (min omega M) + M / logScale N := by
  classical
  let w := min omega M
  have hw : 0 ≤ w := le_min homega hM
  have hrep : ∀ p, |f p - f (P.rep (P.classify p))| ≤ w := by
    intro p
    apply le_min
    · exact hosc _ _ _ rfl (P.classify_rep _)
    · exact abs_le.mpr ⟨by linarith [(hf p).1, (hf (P.rep (P.classify p))).2],
        by linarith [(hf p).2, (hf (P.rep (P.classify p))).1]⟩
  have hcomp : ∀ p, 0 ≤ M-f p ∧ M-f p ≤ M := by
    intro p
    constructor <;> linarith [(hf p).1, (hf p).2]
  have hrepcomp : ∀ p, |(M-f p) - (M-f (P.rep (P.classify p)))| ≤ w := by
    intro p
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hrep p
  have hlow := Compat.one_sided_quadrature cuts hN μ P f hT.le hrho hphi hM hw
    hf hrep hLike hr hrs hs
  have hhigh := Compat.one_sided_quadrature cuts hN μ P (fun p => M-f p)
    hT.le hrho hphi hM hw hcomp hrepcomp hLike hr hrs hs
  have hspatial (t : ℝ) : Integrable f (μ t : Measure (Simplex k)) := by
    apply (integrable_const M).mono' hcont.aestronglyMeasurable
    exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf p).1] using (hf p).2)
  have hfint (t : ℝ) : (∫ p, M-f p ∂(μ t : Measure (Simplex k))) =
      M - ∫ p, f p ∂(μ t : Measure (Simplex k)) := by
    rw [integral_sub (integrable_const M) (hspatial t)]
    simp
  have hrestrict : IntervalIntegrable (fun t => ∫ p, f p ∂(μ t : Measure (Simplex k))) volume r s := by
    apply htime.mono_set
    rw [uIcc_of_le hrs, uIcc_of_le hT.le]
    exact Icc_subset_Icc hr hs
  simp_rw [hfint] at hhigh
  rw [intervalIntegral.integral_sub intervalIntegrable_const hrestrict,
    intervalIntegral.integral_const] at hhigh
  simp only [smul_eq_mul] at hhigh
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hhigh
  have hcount := Compat.timePositions_count_error hN hr hrs hs
  have hcountM := mul_le_mul_of_nonneg_left (abs_le.mp hcount).2 hM
  have hreverse :
      (∑ j ∈ Compat.timePositions N (horizonDepth N T) r s,
        f (cuts.profile (Targets.deckPos hN) j)) / logScale N -
        (∫ t in r..s, ∫ p, f p ∂(μ t : Measure (Simplex k))) ≤
        Compat.quadratureError N T rho phi P.cellCount M w + M / logScale N := by
    rw [sub_div] at hhigh
    have heq : M * (((Compat.timePositions N (horizonDepth N T) r s).card : ℝ) / logScale N - (s-r)) =
        ((Compat.timePositions N (horizonDepth N T) r s).card : ℝ)*M/logScale N - (s-r)*M := by ring
    rw [heq, mul_one_div] at hcountM
    linarith
  apply abs_le.mpr
  exact ⟨by dsimp [w] at hlow ⊢; linarith [div_nonneg hM (logScale_pos hN).le], hreverse⟩

/-- Numerical domination of the two-sided complement estimate by the frozen finite budget. -/
theorem quadrature_budget {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m)
    {T rho phi omega M : ℝ} (hT : 0 ≤ T) (hrho : 0 < rho)
    (_hphi : 0 ≤ phi) (homega : 0 ≤ omega) (hM : 0 ≤ M) :
    Compat.quadratureError N T rho phi m M (min omega M) + 3*M/logScale N ≤
      2*T*omega + M*m*phi*T + 4*M*rho +
        (4*M*m*(T/rho+2)+6*M)/logScale N := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hwM : min omega M ≤ M := min_le_right _ _
  have hwo : min omega M ≤ omega := min_le_left _ _
  have hw0 : 0 ≤ min omega M := le_min homega hM
  have hfloor : (⌊T/rho⌋₊ : ℝ) ≤ T/rho := Nat.floor_le (div_nonneg hT hrho.le)
  have hcoeff : min omega M + M + 2*M*m ≤ 4*M*m := by nlinarith
  have hmul := mul_le_mul hcoeff (by linarith : (⌊T/rho⌋₊ : ℝ)+1 ≤ T/rho+2)
    (by positivity : 0 ≤ (⌊T/rho⌋₊ : ℝ)+1) (by positivity : 0 ≤ 4*M*m)
  have hnum : (min omega M + M + 2*M*m)*((⌊T/rho⌋₊ : ℝ)+1)+3*M ≤
      4*M*m*(T/rho+2)+6*M := by linarith
  have hdiv := div_le_div_of_nonneg_right hnum (logScale_pos hN).le
  have how := mul_le_mul_of_nonneg_right hwo hT
  unfold Compat.quadratureError
  push_cast
  rw [add_div] at hdiv
  nlinarith [mul_nonneg hM hrho.le]

/-- Uniform absolute quadrature under the frozen explicit scalar-integrability premises. -/
theorem genericQuadrature : Targets.GenericQuadrature := by
  intro k N hN T rho phi omega M hT hrho hphi homega hM P μ f hcont hf hosc _hcell htime cuts hLike r s hr hrs hs
  have hST : horizon N (horizonDepth N T) ≤ T := by
    unfold horizon
    linarith [(horizonDepth_error hN hT.le).1]
  have hm : 1 ≤ P.cellCount := by
    obtain ⟨p⟩ := nonempty_of_isProbabilityMeasure (μ 0 : Measure (Simplex k))
    have := (P.classify p).isLt
    omega
  have hsample := sampledQuadrature hN hT hrho hphi homega hM P μ f hcont hf hosc
    htime cuts hLike hr hrs (hs.trans hST)
  have hi := empiricalIntegral_sample_error hN (f := fun j => f (cuts.profile (Targets.deckPos hN) j)) hM
    (fun j => by simpa only [abs_of_nonneg (hf (cuts.profile (Targets.deckPos hN) j)).1]
      using (hf (cuts.profile (Targets.deckPos hN) j)).2) hr hrs hs
  have hinterp :
      |empiricalIntegral N (fun j => f (cuts.profile (Targets.deckPos hN) j)) r s -
        (∑ j ∈ Compat.timePositions N (horizonDepth N T) r s,
          f (cuts.profile (Targets.deckPos hN) j)) / logScale N| ≤ 2*M/logScale N := by
    simpa only [Compat.timePositions] using hi
  calc
    _ ≤ |empiricalIntegral N (fun j => f (cuts.profile (Targets.deckPos hN) j)) r s -
          (∑ j ∈ Compat.timePositions N (horizonDepth N T) r s,
            f (cuts.profile (Targets.deckPos hN) j)) / logScale N| +
        |(∑ j ∈ Compat.timePositions N (horizonDepth N T) r s,
            f (cuts.profile (Targets.deckPos hN) j)) / logScale N -
          ∫ t in r..s, ∫ p, f p ∂(μ t : Measure (Simplex k))| := abs_sub_le _ _ _
    _ ≤ 2*M/logScale N +
        (Compat.quadratureError N T rho phi P.cellCount M (min omega M) + M/logScale N) :=
      add_le_add hinterp hsample
    _ = Compat.quadratureError N T rho phi P.cellCount M (min omega M) + 3*M/logScale N := by ring
    _ ≤ _ := quadrature_budget hN hm hT.le hrho hphi homega hM

end RiffleLowerV2.ProfileTransfer
