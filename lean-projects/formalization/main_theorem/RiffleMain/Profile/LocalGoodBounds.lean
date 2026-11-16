import RiffleMain.Profile.WeakToIntervals
import RiffleMain.Profile.GoodColumns
import RiffleLowerV2.ProfileTransfer.Endpoint

set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped BigOperators
namespace RiffleMain.Profile
open TimeProfile RiffleLowerV2 RiffleLowerV2.ProfileTransfer

theorem maxCost_interval_lower {k : ℕ} (hk : 2 ≤ k) {μ : TimeLaw k}
    (hμ : MeasurableProfile μ) {T a r s : ℝ}
    (hlower : ∀ᵐ t ∂volume.restrict (Icc 0 T), a ≤ profileMaxCost μ t)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ T) :
    a*(s-r) ≤ integratedMaxCost μ r s := by
  have hi : IntervalIntegrable (profileMaxCost μ) volume r s :=
    intervalIntegrable_of_measurable_bounded (measurable_profileMaxCost hμ)
      (M := Real.log (k : ℝ))
      (fun t => by
        rw [abs_of_nonneg (profileMaxCost_bounds hk μ t).1]
        exact (profileMaxCost_bounds hk μ t).2) r s
  have hrestrict : ∀ᵐ t ∂volume.restrict (Icc r s), a ≤ profileMaxCost μ t :=
    ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hr hs) hlower
  have hh := intervalIntegral.integral_mono_ae_restrict hrs
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => a) volume r s) hi hrestrict
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, integratedMaxCost] using hh

theorem clipped_maxCost_interval_error {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) {μ : TimeLaw k} (hμ : MeasurableProfile μ) {T e r s : ℝ}
    (herr : ∀ t ∈ Icc 0 T,
      |empiricalCumulative cuts (by omega) maxCost t - profileCumulative μ maxCost t| ≤ e)
    (hr : r ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    |A cuts (by omega) (min r (horizon N K)) (min s (horizon N K)) -
      integratedMaxCost μ r s| ≤ 2*e := by
  have hqi (a b : ℝ) : IntervalIntegrable (profileMaxCost μ) volume a b :=
    intervalIntegrable_of_measurable_bounded (measurable_profileMaxCost hμ)
      (M := Real.log (k : ℝ))
      (fun t => by
        rw [abs_of_nonneg (profileMaxCost_bounds hk μ t).1]
        exact (profileMaxCost_bounds hk μ t).2) a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hqi 0 r) (hqi r s)
  have hesplit := empiricalIntegral_add N (fun j => maxCost (cuts.profile (by omega) j))
    0 (min r (horizon N K)) (min s (horizon N K))
  have hrerr := herr r hr
  have hserr := herr s hs
  dsimp [empiricalCumulative, profileCumulative, profileMaxCost] at hrerr hserr hsplit
  apply abs_le.mpr
  dsimp [A, integratedMaxCost, profileMaxCost]
  constructor <;> linarith [(abs_le.mp hrerr).1, (abs_le.mp hrerr).2,
    (abs_le.mp hserr).1, (abs_le.mp hserr).2]

/-- Large empirical max-cost mass forces many good columns, with two-column
rounding loss.  The conclusion uses the paper's closed time windows. -/
theorem maxCost_interval_upper {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) {a ρ b : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (hb : 0 < b) :
    A cuts (by omega) (min a (horizon N K)) (min (a+ρ) (horizon N K)) ≤
      (b/4)*ρ + Real.log (k : ℝ) *
        ((((Finset.univ.filter fun j : Fin K =>
          a ≤ columnTime N j ∧ columnTime N j ≤ a+ρ ∧
            GoodColumn (cuts.profile (by omega) j) (goodThreshold k b)).card : ℝ) /
          logScale N) + 2/logScale N) := by
  classical
  let Lk := Real.log (k : ℝ)
  let r := min a (horizon N K)
  let s := min (a+ρ) (horizon N K)
  let d : Fin K → ℝ := fun j =>
    if GoodColumn (cuts.profile (by omega) j) (goodThreshold k b) then 1 else 0
  let J := Finset.univ.filter fun j : Fin K =>
    a ≤ columnTime N j ∧ columnTime N j ≤ a+ρ ∧
      GoodColumn (cuts.profile (by omega) j) (goodThreshold k b)
  have hL := logScale_pos hN
  have hLk : 0 ≤ Lk := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hS : 0 ≤ horizon N K := div_nonneg (Nat.cast_nonneg _) hL.le
  have hr : 0 ≤ r := le_min ha hS
  have hrs : r ≤ s := min_le_min_right _ (by linarith)
  have hs : s ≤ horizon N K := min_le_right _ _
  have hsr : s-r ≤ ρ := by
    have hh := abs_min_sub_min_le (a+ρ) a (horizon N K)
    rw [abs_of_nonneg (sub_nonneg.mpr hrs)] at hh
    have heq : a+ρ-a = ρ := by ring
    rw [heq, abs_of_pos hρ] at hh
    exact hh
  have hcost (j : Fin K) : maxCost (cuts.profile (by omega) j) ≤ b/4+Lk*d j := by
    by_cases hj : GoodColumn (cuts.profile (by omega) j) (goodThreshold k b)
    · simp only [d, if_pos hj, mul_one]
      have hh := (maxCost_bounds hk (cuts.profile (by omega) j)).2
      dsimp [Lk]; linarith
    · simp only [d, if_neg hj, mul_zero, add_zero]
      exact (goodThreshold_spec hk hb).2.2 _ hj
  have hmono := empiricalIntegral_mono hN hcost hrs
  have heq : empiricalIntegral N (fun j => b/4+Lk*d j) r s =
      (s-r)*(b/4)+Lk*empiricalIntegral N d r s := by
    have hconst := empiricalIntegral_const hN (b/4) ⟨hr, hrs.trans hs⟩
      ⟨hr.trans hrs, hs⟩
    rw [← hconst]
    simp only [empiricalIntegral, mul_add, add_div, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at hmono
  have hd : ∀ j, |d j| ≤ 1 := by intro j; dsimp [d]; split_ifs <;> norm_num
  have hsample := empiricalIntegral_sample_error hN (by norm_num : (0 : ℝ) ≤ 1) hd hr hrs hs
  let J' := Finset.univ.filter fun j : Fin K =>
    r < columnTime N j ∧ columnTime N j ≤ s ∧
      GoodColumn (cuts.profile (by omega) j) (goodThreshold k b)
  have hcard : (∑ j ∈ Finset.univ.filter (fun j : Fin K =>
      r < columnTime N j ∧ columnTime N j ≤ s), d j) = (J'.card : ℝ) := by
    simp [d, J', Finset.sum_ite, Finset.filter_filter, and_assoc]
  rw [hcard] at hsample
  have hsub : J' ⊆ J := by
    intro j hj
    obtain ⟨_, hrt, hts, hjgood⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, hts.trans (min_le_left _ _), hjgood⟩
    by_cases haS : a ≤ horizon N K
    · have hrEq : r = a := min_eq_left haS
      rw [hrEq] at hrt
      exact hrt.le
    · have hrEq : r = horizon N K := min_eq_right (not_le.mp haS).le
      rw [hrEq] at hrt
      exact False.elim (not_lt_of_ge (hts.trans hs) hrt)
  have hcardle : (J'.card : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  have hIbound : empiricalIntegral N d r s ≤ (J.card : ℝ)/logScale N+2/logScale N := by
    have hh := (abs_le.mp hsample).2
    have hh' := div_le_div_of_nonneg_right hcardle hL.le
    linarith
  have hIbound' := mul_le_mul_of_nonneg_left hIbound hLk
  have hbase := mul_le_mul_of_nonneg_right hsr (show 0 ≤ b/4 by positivity)
  change empiricalIntegral N (fun j => maxCost (cuts.profile (by omega) j)) r s ≤
    (b/4)*ρ+Lk*((J.card : ℝ)/logScale N+2/logScale N)
  nlinarith

end RiffleMain.Profile
