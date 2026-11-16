/- Provenance: fresh source port of ../time_profile/RiffleTimeProfile/LatticeCounts.lean. Namespace and imports adapted only. -/
import RiffleTimeProfile.Base
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace RiffleLowerV2.ProfileTransfer.Compat
open TimeProfile

/-- The disjoint convention used to count sampled columns in a time interval. -/
def timePositions (N K : ℕ) (a b : ℝ) : Finset (Fin K) := by
  classical
  exact Finset.univ.filter fun j => a < columnTime N j ∧ columnTime N j ≤ b

@[simp] theorem mem_timePositions {N K : ℕ} {a b : ℝ} {j : Fin K} :
    j ∈ timePositions N K a b ↔ a < columnTime N j ∧ columnTime N j ≤ b := by
  classical
  simp [timePositions]

/-- A spatial cell count with the half-open time convention. -/
def timeCellCount {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (a b : ℝ) (i : Fin P.cellCount) : ℕ := by
  classical
  exact ((timePositions N K a b).filter fun j =>
    P.classify (cuts.profile hN j) = i).card

theorem mem_timePositions_iff_floor {N K : ℕ} (hN : 2 ≤ N) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (j : Fin K) :
    j ∈ timePositions N K a b ↔
      ⌊a * logScale N⌋₊ < j.val + 1 ∧ j.val + 1 ≤ ⌊b * logScale N⌋₊ := by
  have hL := logScale_pos hN
  have haL := mul_nonneg ha hL.le
  have hbL := mul_nonneg (ha.trans hab) hL.le
  rw [mem_timePositions]
  simp only [columnTime, lt_div_iff₀ hL, div_le_iff₀ hL,
    Nat.floor_lt haL, Nat.le_floor_iff hbL, Nat.cast_add, Nat.cast_one]

theorem timePositions_card {N : ℕ} (hN : 2 ≤ N) {T a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) :
    (timePositions N (horizonDepth N T) a b).card =
      ⌊b * logScale N⌋₊ - ⌊a * logScale N⌋₊ := by
  classical
  rw [← Nat.card_Ioc]
  apply Finset.card_bij (fun j _ => j.val + 1)
  · intro j hj
    exact Finset.mem_Ioc.mpr ((mem_timePositions_iff_floor hN ha hab j).mp hj)
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro q hq
    have hq' := Finset.mem_Ioc.mp hq
    have hqpos : 0 < q := by omega
    have hqbound : q ≤ horizonDepth N T :=
      hq'.2.trans (Nat.floor_mono (mul_le_mul_of_nonneg_right hbT (logScale_pos hN).le))
    let j : Fin (horizonDepth N T) := ⟨q - 1, by omega⟩
    have hjval : j.val + 1 = q := by dsimp [j]; omega
    refine ⟨j, ?_, hjval⟩
    apply (mem_timePositions_iff_floor hN ha hab j).mpr
    simpa only [hjval] using hq'

theorem timePositions_count_error {N : ℕ} (hN : 2 ≤ N) {T a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) :
    |((timePositions N (horizonDepth N T) a b).card : ℝ) / logScale N -
      (b - a)| ≤ 1 / logScale N := by
  have hL := logScale_pos hN
  have haL := mul_nonneg ha hL.le
  have hbL := mul_nonneg (ha.trans hab) hL.le
  have hmono := Nat.floor_mono (mul_le_mul_of_nonneg_right hab hL.le)
  rw [timePositions_card hN ha hab hbT, Nat.cast_sub hmono]
  have hfa := Nat.floor_le haL
  have hfb := Nat.floor_le hbL
  have hfa' := Nat.lt_floor_add_one (a * logScale N)
  have hfb' := Nat.lt_floor_add_one (b * logScale N)
  have hnum : |(⌊b * logScale N⌋₊ : ℝ) - (⌊a * logScale N⌋₊ : ℝ) -
      (b - a) * logScale N| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have heq : ((⌊b * logScale N⌋₊ : ℝ) - (⌊a * logScale N⌋₊ : ℝ)) /
      logScale N - (b - a) =
      ((⌊b * logScale N⌋₊ : ℝ) - (⌊a * logScale N⌋₊ : ℝ) -
        (b - a) * logScale N) / logScale N := by
    field_simp
  rw [heq, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right hnum hL.le

theorem sum_timeCellCount {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (a b : ℝ) :
    (∑ i, timeCellCount cuts hN P a b i) = (timePositions N K a b).card := by
  classical
  simpa only [timeCellCount] using
    (Finset.card_eq_sum_card_fiberwise
      (s := timePositions N K a b) (t := Finset.univ)
      (f := fun j => P.classify (cuts.profile hN j))
      (fun _ _ => Finset.mem_univ _)).symm

theorem sum_timeCellCount_real {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (a b : ℝ) :
    (∑ i, (timeCellCount cuts hN P a b i : ℝ) / logScale N) =
      ((timePositions N K a b).card : ℝ) / logScale N := by
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast sum_timeCellCount cuts hN P a b

theorem timeCellCount_weighted_sum_raw {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (a b : ℝ) (weight : Fin P.cellCount → ℝ) :
    (∑ i, weight i * (timeCellCount cuts hN P a b i : ℝ)) =
      ∑ j ∈ timePositions N K a b, weight (P.classify (cuts.profile hN j)) := by
  classical
  simpa only [timeCellCount, Finset.sum_const, nsmul_eq_mul, mul_comm] using
    (Finset.sum_fiberwise_of_maps_to'
      (s := timePositions N K a b) (t := Finset.univ)
      (g := fun j => P.classify (cuts.profile hN j))
      (fun _ _ => Finset.mem_univ _) weight)

theorem timeCellCount_weighted_sum {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (a b : ℝ) (weight : Fin P.cellCount → ℝ) :
    (∑ i, weight i * ((timeCellCount cuts hN P a b i : ℝ) / logScale N)) =
      (∑ j ∈ timePositions N K a b, weight (P.classify (cuts.profile hN j))) /
        logScale N := by
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, timeCellCount_weighted_sum_raw]

theorem columnTime_injective {N K : ℕ} (hN : 2 ≤ N) :
    Function.Injective (columnTime (K := K) N) := by
  intro i j hij
  apply Fin.ext
  have hval : (i.val : ℝ) + 1 = (j.val : ℝ) + 1 :=
    (div_left_inj' (logScale_pos hN).ne').mp hij
  exact_mod_cast (add_right_cancel hval)

theorem timeCellCount_closed_bounds {k N K : ℕ} (cuts : Cuts k N K) (hN : 2 ≤ N)
    (P : BorelPartition k) (a b : ℝ) (i : Fin P.cellCount) :
    timeCellCount cuts (by omega) P a b i ≤ intervalCount cuts (by omega) P a b i ∧
      intervalCount cuts (by omega) P a b i ≤ timeCellCount cuts (by omega) P a b i + 1 := by
  classical
  let closed : Finset (Fin K) := Finset.univ.filter fun j =>
    a ≤ columnTime N j ∧ columnTime N j ≤ b ∧ P.classify (cuts.profile (by omega) j) = i
  let halfOpen : Finset (Fin K) := (timePositions N K a b).filter fun j =>
    P.classify (cuts.profile (by omega) j) = i
  have hsub : halfOpen ⊆ closed := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have ht := mem_timePositions.mp hj'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.1.le, ht.2, hj'.2⟩
  have hboundary : ∀ j ∈ closed \ halfOpen, columnTime N j = a := by
    intro j hj
    have hj' := Finset.mem_sdiff.mp hj
    have hclosed := (Finset.mem_filter.mp hj'.1).2
    have hnlt : ¬ a < columnTime N j := by
      intro hlt
      apply hj'.2
      exact Finset.mem_filter.mpr
        ⟨mem_timePositions.mpr ⟨hlt, hclosed.2.1⟩, hclosed.2.2⟩
    exact le_antisymm (le_of_not_gt hnlt) hclosed.1
  have hdcard : (closed \ halfOpen).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj j' hj'
    apply columnTime_injective hN
    exact (hboundary j hj).trans (hboundary j' hj').symm
  have hmono := Finset.card_mono hsub
  have hsum := Finset.card_sdiff_add_card_eq_card hsub
  change halfOpen.card ≤ closed.card ∧ closed.card ≤ halfOpen.card + 1
  omega

theorem timeCellCount_closed_error {k N K : ℕ} (cuts : Cuts k N K) (hN : 2 ≤ N)
    (P : BorelPartition k) (a b : ℝ) (i : Fin P.cellCount) :
    |(intervalCount cuts (by omega) P a b i : ℝ) / logScale N -
      (timeCellCount cuts (by omega) P a b i : ℝ) / logScale N| ≤ 1 / logScale N := by
  have hL := logScale_pos hN
  have hb := timeCellCount_closed_bounds cuts hN P a b i
  have hlo : (timeCellCount cuts (by omega) P a b i : ℝ) ≤
      (intervalCount cuts (by omega) P a b i : ℝ) := by exact_mod_cast hb.1
  have hhi : (intervalCount cuts (by omega) P a b i : ℝ) ≤
      (timeCellCount cuts (by omega) P a b i : ℝ) + 1 := by exact_mod_cast hb.2
  rw [← sub_div, abs_div, abs_of_pos hL, abs_of_nonneg (sub_nonneg.mpr hlo)]
  apply div_le_div_of_nonneg_right _ hL.le
  linarith

theorem AlmostLike.timeCellCount_error {k N K : ℕ} {cuts : Cuts k N K} {hN : 0 < N}
    {mu : TimeLaw k} {P : BorelPartition k} {T rho phi : ℝ}
    (hLike : AlmostLike cuts hN mu P T rho phi) (hN2 : 2 ≤ N) (hrho : 0 < rho)
    {a : ℝ} (ha : 0 ≤ a) (hgrid : ∃ z : ℤ, a = rho * z) (hfull : a + rho ≤ T)
    (i : Fin P.cellCount) :
    |(timeCellCount cuts hN P a (a + rho) i : ℝ) / logScale N -
      ∫ t in a..a + rho, cellMass mu P i t| ≤ phi * rho + 2 / logScale N := by
  have hmin : min (a + rho) T = a + rho := min_eq_left hfull
  have hblock := hLike a hgrid ha (by rw [hmin]; linarith) i
  rw [hmin] at hblock
  have hendpoint := timeCellCount_closed_error cuts hN2 P a (a + rho) i
  rw [abs_sub_comm] at hendpoint
  calc
    _ ≤ |(timeCellCount cuts hN P a (a + rho) i : ℝ) / logScale N -
          (intervalCount cuts hN P a (a + rho) i : ℝ) / logScale N| +
        |(intervalCount cuts hN P a (a + rho) i : ℝ) / logScale N -
          ∫ t in a..a + rho, cellMass mu P i t| := abs_sub_le _ _ _
    _ ≤ 1 / logScale N + (phi * (a + rho - a) + 1 / logScale N) :=
      add_le_add hendpoint hblock
    _ = phi * rho + 2 / logScale N := by ring

end RiffleLowerV2.ProfileTransfer.Compat
