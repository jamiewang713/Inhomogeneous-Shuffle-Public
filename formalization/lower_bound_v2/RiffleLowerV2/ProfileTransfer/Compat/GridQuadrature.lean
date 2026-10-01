/- Provenance: fresh source port of ../time_profile/RiffleTimeProfile/GridQuadrature.lean. Namespace and imports adapted only. -/
import RiffleLowerV2.ProfileTransfer.Compat.LatticeCounts
import RiffleLowerV2.ProfileTransfer.Compat.IntegralEnvelope
import RiffleLowerV2.ProfileTransfer.Compat.Error

set_option autoImplicit false

noncomputable section
open Set MeasureTheory

namespace RiffleLowerV2.ProfileTransfer.Compat
open TimeProfile

private def sampleWindow {K : ℕ} (time : Fin K → ℝ) (a b : ℝ) : Finset (Fin K) := by
  classical
  exact Finset.univ.filter fun j => a < time j ∧ time j ≤ b

private theorem sampleWindow_nonneg {K : ℕ} (time : Fin K → ℝ) (g : Fin K → ℝ)
    (hg : ∀ j, 0 ≤ g j) (a b : ℝ) :
    0 ≤ ∑ j ∈ sampleWindow time a b, g j := by
  exact Finset.sum_nonneg fun j _ => hg j

private theorem sum_grid_samples_le {K : ℕ} (time : Fin K → ℝ) (g : Fin K → ℝ)
    (hg : ∀ j, 0 ≤ g j) {rho a b : ℝ} (hrho : 0 < rho)
    {lo hi : ℕ} (ha : a ≤ (lo : ℝ) * rho) (hb : (hi : ℝ) * rho ≤ b) :
    (∑ q ∈ Finset.Ico lo hi,
      ∑ j ∈ sampleWindow time ((q : ℝ) * rho) (((q : ℝ) + 1) * rho), g j) ≤
      ∑ j ∈ sampleWindow time a b, g j := by
  classical
  let blocks := fun q : ℕ =>
    sampleWindow time ((q : ℝ) * rho) (((q : ℝ) + 1) * rho)
  have hdisjoint : Set.PairwiseDisjoint (↑(Finset.Ico lo hi) : Set ℕ) blocks := by
    intro q _ q' _ hne
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have hq := (Finset.mem_filter.mp hj).2
    have hq' := (Finset.mem_filter.mp hj').2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hcast : (q : ℝ) + 1 ≤ (q' : ℝ) := by exact_mod_cast hlt
      have hm := mul_le_mul_of_nonneg_right hcast hrho.le
      linarith
    · have hcast : (q' : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hgt
      have hm := mul_le_mul_of_nonneg_right hcast hrho.le
      linarith
  have hsub : (Finset.Ico lo hi).biUnion blocks ⊆ sampleWindow time a b := by
    intro j hj
    rcases Finset.mem_biUnion.mp hj with ⟨q, hq, hj⟩
    have hq' := Finset.mem_Ico.mp hq
    have hlo : (lo : ℝ) ≤ q := by exact_mod_cast hq'.1
    have hhi : (q : ℝ) + 1 ≤ hi := by exact_mod_cast hq'.2
    have htime := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hl := mul_le_mul_of_nonneg_right hlo hrho.le
    have hu := mul_le_mul_of_nonneg_right hhi hrho.le
    constructor <;> linarith
  rw [← Finset.sum_biUnion hdisjoint]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hg j

private theorem interval_integral_le_constant {F : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hF : IntervalIntegrable F volume a b)
    (hbound : ∀ t, F t ≤ M) :
    (∫ t in a..b, F t) ≤ M * (b - a) := by
  have h := intervalIntegral.integral_mono_on hab hF
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume a b)
    (fun t _ => hbound t)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

private theorem grid_integral_assembly {K : ℕ} (time : Fin K → ℝ)
    (F : ℝ → ℝ) (g : Fin K → ℝ) {L T rho M A B a b : ℝ}
    (hL : 0 < L) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ t, 0 ≤ F t ∧ F t ≤ M) (hg : ∀ j, 0 ≤ g j)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hblock : ∀ q : ℕ, a ≤ (q : ℝ) * rho → ((q : ℝ) + 1) * rho ≤ b →
      (∫ t in (q : ℝ) * rho..((q : ℝ) + 1) * rho, F t) ≤
        (∑ j ∈ sampleWindow time ((q : ℝ) * rho) (((q : ℝ) + 1) * rho), g j) / L +
          A * rho + B / L) :
    (∫ t in a..b, F t) ≤
      (∑ j ∈ sampleWindow time a b, g j) / L + A * T + 2 * M * rho +
        B * ((⌊T / rho⌋₊ : ℝ) + 1) / L := by
  classical
  have hsum0 := sampleWindow_nonneg time g hg a b
  have hrest : 0 ≤ A * T + 2 * M * rho + B * ((⌊T / rho⌋₊ : ℝ) + 1) / L := by
    positivity
  by_cases hint : IntervalIntegrable F volume a b
  · let lo : ℕ := ⌈a / rho⌉₊
    let hi : ℕ := ⌊b / rho⌋₊
    have hb0 : 0 ≤ b := ha.trans hab
    have halow : a ≤ (lo : ℝ) * rho := by
      exact (div_le_iff₀ hrho).mp (Nat.le_ceil (a / rho))
    have hahigh : (lo : ℝ) * rho < a + rho := by
      have h := Nat.ceil_lt_add_one (div_nonneg ha hrho.le)
      have hm := mul_lt_mul_of_pos_right h hrho
      simpa only [add_mul, div_mul_cancel₀ _ hrho.ne', one_mul] using hm
    have hblow : (hi : ℝ) * rho ≤ b := by
      exact (le_div_iff₀ hrho).mp (Nat.floor_le (div_nonneg hb0 hrho.le))
    have hbhigh : b < ((hi : ℝ) + 1) * rho := by
      exact (div_lt_iff₀ hrho).mp (Nat.lt_floor_add_one (b / rho))
    have hrestrict : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
        IntervalIntegrable F volume x y := by
      intro x y hax hxy hyb
      apply hint.mono_set
      rw [uIcc_of_le hxy, uIcc_of_le hab]
      exact Icc_subset_Icc hax hyb
    by_cases horder : lo ≤ hi
    · have horderR : (lo : ℝ) ≤ hi := by exact_mod_cast horder
      have huv : (lo : ℝ) * rho ≤ (hi : ℝ) * rho :=
        mul_le_mul_of_nonneg_right horderR hrho.le
      have hau := halow
      have hub : (lo : ℝ) * rho ≤ b := huv.trans hblow
      have hav : a ≤ (hi : ℝ) * rho := halow.trans huv
      have hleft := hrestrict a ((lo : ℝ) * rho) le_rfl halow hub
      have hmiddle := hrestrict ((lo : ℝ) * rho) ((hi : ℝ) * rho) halow huv hblow
      have hright := hrestrict ((hi : ℝ) * rho) b hav hblow le_rfl
      have hqbounds : ∀ q ∈ Finset.Ico lo hi,
          a ≤ (q : ℝ) * rho ∧ ((q : ℝ) + 1) * rho ≤ b := by
        intro q hq
        have hq' := Finset.mem_Ico.mp hq
        have hql : (lo : ℝ) ≤ q := by exact_mod_cast hq'.1
        have hqu : (q : ℝ) + 1 ≤ hi := by exact_mod_cast hq'.2
        exact ⟨halow.trans (mul_le_mul_of_nonneg_right hql hrho.le),
          (mul_le_mul_of_nonneg_right hqu hrho.le).trans hblow⟩
      have hqint : ∀ q ∈ Finset.Ico lo hi,
          IntervalIntegrable F volume ((q : ℝ) * rho) (((q : ℝ) + 1) * rho) := by
        intro q hq
        obtain ⟨hqa, hqb⟩ := hqbounds q hq
        apply hrestrict _ _ hqa _ hqb
        nlinarith
      have hsumint :
          (∑ q ∈ Finset.Ico lo hi,
            ∫ t in (q : ℝ) * rho..((q : ℝ) + 1) * rho, F t) =
            ∫ t in (lo : ℝ) * rho..(hi : ℝ) * rho, F t := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (intervalIntegral.sum_integral_adjacent_intervals_Ico
            (a := fun q : ℕ => (q : ℝ) * rho) horder
            (fun q hq => by
              simpa only [Nat.cast_add, Nat.cast_one] using
                hqint q (Finset.mem_Ico.mpr hq)))
      have hsumineq := Finset.sum_le_sum fun q hq =>
        hblock q (hqbounds q hq).1 (hqbounds q hq).2
      have hsumform :
          (∑ q ∈ Finset.Ico lo hi,
            ((∑ j ∈ sampleWindow time ((q : ℝ) * rho) (((q : ℝ) + 1) * rho), g j) / L +
              A * rho + B / L)) =
          (∑ q ∈ Finset.Ico lo hi,
            ∑ j ∈ sampleWindow time ((q : ℝ) * rho) (((q : ℝ) + 1) * rho), g j) / L +
            (A * rho + B / L) * ((hi : ℝ) - lo) := by
        simp only [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const,
          Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub horder]
        ring
      rw [hsumint, hsumform] at hsumineq
      have hemp := div_le_div_of_nonneg_right
        (sum_grid_samples_le time g hg hrho halow hblow) hL.le
      have hlength : rho * ((hi : ℝ) - lo) ≤ T := by nlinarith
      have hhiT : hi ≤ ⌊T / rho⌋₊ :=
        Nat.floor_mono ((div_le_div_iff_of_pos_right hrho).mpr hb)
      have hhiTR : (hi : ℝ) ≤ (⌊T / rho⌋₊ : ℝ) := by exact_mod_cast hhiT
      have hcount : (hi : ℝ) - lo ≤ (⌊T / rho⌋₊ : ℝ) + 1 := by
        have hlo0 : 0 ≤ (lo : ℝ) := Nat.cast_nonneg lo
        linarith
      have hlargeA := mul_le_mul_of_nonneg_left hlength hA
      have hlargeB := mul_le_mul_of_nonneg_left hcount (div_nonneg hB hL.le)
      have hmiderror : (A * rho + B / L) * ((hi : ℝ) - lo) ≤
          A * T + B * ((⌊T / rho⌋₊ : ℝ) + 1) / L := by
        calc
          _ = A * (rho * ((hi : ℝ) - lo)) + B / L * ((hi : ℝ) - lo) := by ring
          _ ≤ A * T + B / L * ((⌊T / rho⌋₊ : ℝ) + 1) := add_le_add hlargeA hlargeB
          _ = _ := by ring
      have hmidbound := hsumineq.trans (add_le_add hemp hmiderror)
      have hleftbound := interval_integral_le_constant halow hleft (fun t => (hF t).2)
      have hrightbound := interval_integral_le_constant hblow hright (fun t => (hF t).2)
      have hboundary : M * ((lo : ℝ) * rho - a) + M * (b - (hi : ℝ) * rho) ≤
          2 * M * rho := by
        have hgap : ((lo : ℝ) * rho - a) + (b - (hi : ℝ) * rho) ≤ 2 * rho := by
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hgap hM]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hleft.trans hmiddle) hright
      rw [← intervalIntegral.integral_add_adjacent_intervals hleft hmiddle] at hsplit
      linarith [hmidbound]
    · have horder' : hi < lo := Nat.lt_of_not_ge horder
      have hstep : (hi : ℝ) + 1 ≤ lo := by exact_mod_cast horder'
      have hmul := mul_le_mul_of_nonneg_right hstep hrho.le
      have hshort : b - a ≤ 2 * rho := by linarith
      have hbnd := interval_integral_le_constant hab hint (fun t => (hF t).2)
      have hsmall := mul_le_mul_of_nonneg_left hshort hM
      have hemp : 0 ≤ (∑ j ∈ sampleWindow time a b, g j) / L := div_nonneg hsum0 hL.le
      have hothers : 0 ≤ A * T + B * ((⌊T / rho⌋₊ : ℝ) + 1) / L := by positivity
      nlinarith
  · rw [intervalIntegral.integral_undef hint]
    exact le_trans (by positivity : 0 ≤
      (∑ j ∈ sampleWindow time a b, g j) / L +
        (A * T + 2 * M * rho + B * ((⌊T / rho⌋₊ : ℝ) + 1) / L)) (by ring_nf; rfl)

private theorem representative_grid_block {k N : ℕ} {T rho phi M omega a : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N)
    (mu : TimeLaw k) (P : BorelPartition k) (f : Simplex k → ℝ)
    (hrho : 0 < rho) (hphi : 0 ≤ phi) (hM : 0 ≤ M) (homega : 0 ≤ omega)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M)
    (herr : ∀ p, |f p - f (P.rep (P.classify p))| ≤ omega)
    (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (ha : 0 ≤ a) (hgrid : ∃ z : ℤ, a = rho * z) (hfull : a + rho ≤ T) :
    (∫ t in a..a + rho, ∫ p, f p ∂(mu t : Measure (Simplex k))) ≤
      (∑ j ∈ timePositions N (horizonDepth N T) a (a + rho),
        f (P.rep (P.classify (cuts.profile (by omega) j)))) / logScale N +
      omega * rho + M * (1 / logScale N + (P.cellCount : ℝ) * (phi * rho + 2 / logScale N)) := by
  classical
  have hL := logScale_pos hN
  have hab : a ≤ a + rho := by linarith
  have htotal := timePositions_count_error hN ha hab hfull
  have hmass : (a + rho - a) -
      (∑ i, (timeCellCount cuts (by omega) P a (a + rho) i : ℝ) / logScale N) ≤
        1 / logScale N := by
    rw [sum_timeCellCount_real]
    have hlo := (abs_le.mp htotal).1
    linarith
  have henv := interval_integral_envelope_of_counts a (a + rho) hab
    (cellMass mu P) (fun i => f (P.rep i))
    (fun t => ∫ p, f p ∂(mu t : Measure (Simplex k))) hM homega
    (fun i t => (cellMass_bounds mu P i t).1) (sum_cellMass mu P)
    (fun i => hf (P.rep i))
    (fun t => (probability_integral_bounds (mu t) f hM hf).1)
    (fun t => probability_integral_le_cell_sum P (mu t) f hM homega hf herr)
    (fun i => (timeCellCount cuts (by omega) P a (a + rho) i : ℝ) / logScale N)
    (by positivity : 0 ≤ phi * rho + 2 / logScale N)
    (AlmostLike.timeCellCount_error hLike hN hrho ha hgrid hfull) hmass
  rw [timeCellCount_weighted_sum] at henv
  simpa only [add_sub_cancel_left, Fintype.card_fin] using henv

/-- C04: a representative cost sum bounds the literal totalized profile integral below. -/
theorem one_sided_quadrature_representative {k N : ℕ} {T rho phi M omega a b : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N)
    (mu : TimeLaw k) (P : BorelPartition k) (f : Simplex k → ℝ)
    (hT : 0 ≤ T) (hrho : 0 < rho) (hphi : 0 ≤ phi)
    (hM : 0 ≤ M) (homega : 0 ≤ omega)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M)
    (herr : ∀ p, |f p - f (P.rep (P.classify p))| ≤ omega)
    (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ t in a..b, ∫ p, f p ∂(mu t : Measure (Simplex k))) ≤
      (∑ j ∈ timePositions N (horizonDepth N T) a b,
        f (P.rep (P.classify (cuts.profile (by omega) j)))) / logScale N +
      quadratureError N T rho phi P.cellCount M omega := by
  classical
  have hL := logScale_pos hN
  let F : ℝ → ℝ := fun t => ∫ p, f p ∂(mu t : Measure (Simplex k))
  let g : Fin (horizonDepth N T) → ℝ :=
    fun j => f (P.rep (P.classify (cuts.profile (by omega) j)))
  have hblock : ∀ q : ℕ, a ≤ (q : ℝ) * rho → ((q : ℝ) + 1) * rho ≤ b →
      (∫ t in (q : ℝ) * rho..((q : ℝ) + 1) * rho, F t) ≤
        (∑ j ∈ sampleWindow (columnTime N) ((q : ℝ) * rho) (((q : ℝ) + 1) * rho), g j) /
            logScale N +
          (2 * omega + M * (P.cellCount : ℝ) * phi) * rho +
            (omega + M + 2 * M * (P.cellCount : ℝ)) / logScale N := by
    intro q hqa hqb
    have hq0 : 0 ≤ (q : ℝ) * rho := by positivity
    have hgrid : ∃ z : ℤ, (q : ℝ) * rho = rho * z := by
      refine ⟨q, ?_⟩
      push_cast
      ring
    have hfull : (q : ℝ) * rho + rho ≤ T := by nlinarith
    have hquad := representative_grid_block cuts hN mu P f hrho hphi hM homega
      hf herr hLike hq0 hgrid hfull
    have heq : ((q : ℝ) + 1) * rho = (q : ℝ) * rho + rho := by ring
    change (∫ t in (q : ℝ) * rho..((q : ℝ) + 1) * rho,
      ∫ p, f p ∂(mu t : Measure (Simplex k))) ≤ _
    rw [heq]
    change (∫ t in (q : ℝ) * rho..(q : ℝ) * rho + rho,
      ∫ p, f p ∂(mu t : Measure (Simplex k))) ≤
      (∑ j ∈ timePositions N (horizonDepth N T) ((q : ℝ) * rho) ((q : ℝ) * rho + rho),
        f (P.rep (P.classify (cuts.profile (by omega) j)))) / logScale N +
        (2 * omega + M * (P.cellCount : ℝ) * phi) * rho +
          (omega + M + 2 * M * (P.cellCount : ℝ)) / logScale N
    calc
      _ ≤ _ := hquad
      _ ≤ _ := by
        have hp : 0 ≤ omega * rho + omega / logScale N := by positivity
        have hnorm :
            omega * rho + M * (1 / logScale N + (P.cellCount : ℝ) *
              (phi * rho + 2 / logScale N)) + (omega * rho + omega / logScale N) =
            (2 * omega + M * (P.cellCount : ℝ) * phi) * rho +
              (omega + M + 2 * M * (P.cellCount : ℝ)) / logScale N := by ring
        linarith
  have hout := grid_integral_assembly (columnTime N) F g hL hT hrho hM
    (by positivity : 0 ≤ 2 * omega + M * (P.cellCount : ℝ) * phi)
    (by positivity : 0 ≤ omega + M + 2 * M * (P.cellCount : ℝ))
    (fun t => probability_integral_bounds (mu t) f hM hf)
    (fun j => (hf (P.rep (P.classify (cuts.profile (by omega) j)))).1)
    ha hab hb hblock
  change (∫ t in a..b, ∫ p, f p ∂(mu t : Measure (Simplex k))) ≤ _ at hout
  have heq : (2 * omega + M * (P.cellCount : ℝ) * phi) * T + 2 * M * rho +
      (omega + M + 2 * M * (P.cellCount : ℝ)) * ((⌊T / rho⌋₊ : ℝ) + 1) / logScale N =
        quadratureError N T rho phi P.cellCount M omega := by
    simp only [quadratureError, Nat.cast_add, Nat.cast_one]
    ring
  calc
    _ ≤ _ := hout
    _ = _ := by
      dsimp only [sampleWindow, timePositions, g]
      rw [← heq]
      ring

/-- C04: actual nonnegative sampled costs bound the totalized profile integral below. -/
theorem one_sided_quadrature {k N : ℕ} {T rho phi M omega a b : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N)
    (mu : TimeLaw k) (P : BorelPartition k) (f : Simplex k → ℝ)
    (hT : 0 ≤ T) (hrho : 0 < rho) (hphi : 0 ≤ phi)
    (hM : 0 ≤ M) (homega : 0 ≤ omega)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ M)
    (herr : ∀ p, |f p - f (P.rep (P.classify p))| ≤ omega)
    (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ t in a..b, ∫ p, f p ∂(mu t : Measure (Simplex k))) ≤
      (∑ j ∈ timePositions N (horizonDepth N T) a b,
        f (cuts.profile (by omega) j)) / logScale N +
      quadratureError N T rho phi P.cellCount M omega := by
  classical
  have hL := logScale_pos hN
  let F : ℝ → ℝ := fun t => ∫ p, f p ∂(mu t : Measure (Simplex k))
  let g : Fin (horizonDepth N T) → ℝ := fun j => f (cuts.profile (by omega) j)
  have hblock : ∀ q : ℕ, a ≤ (q : ℝ) * rho → ((q : ℝ) + 1) * rho ≤ b →
      (∫ t in (q : ℝ) * rho..((q : ℝ) + 1) * rho, F t) ≤
        (∑ j ∈ sampleWindow (columnTime N) ((q : ℝ) * rho) (((q : ℝ) + 1) * rho), g j) /
            logScale N +
          (2 * omega + M * (P.cellCount : ℝ) * phi) * rho +
            (omega + M + 2 * M * (P.cellCount : ℝ)) / logScale N := by
    intro q hqa hqb
    have hq0 : 0 ≤ (q : ℝ) * rho := by positivity
    have hgrid : ∃ z : ℤ, (q : ℝ) * rho = rho * z := by
      refine ⟨q, ?_⟩
      push_cast
      ring
    have hfull : (q : ℝ) * rho + rho ≤ T := by nlinarith
    have hquad := representative_grid_block cuts hN mu P f hrho hphi hM homega
      hf herr hLike hq0 hgrid hfull
    let s := timePositions N (horizonDepth N T) ((q : ℝ) * rho) ((q : ℝ) * rho + rho)
    have hreplace : (∑ j ∈ s, f (P.rep (P.classify (cuts.profile (by omega) j)))) ≤
        (∑ j ∈ s, f (cuts.profile (by omega) j)) + omega * (s.card : ℝ) := by
      have h := Finset.sum_le_sum (s := s) (fun j _ =>
        show f (P.rep (P.classify (cuts.profile (by omega) j))) ≤
            f (cuts.profile (by omega) j) + omega from by
          have hp := (abs_le.mp (herr (cuts.profile (by omega) j))).1
          linarith)
      simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm] using h
    have htotal := timePositions_count_error hN hq0 (by linarith :
      (q : ℝ) * rho ≤ (q : ℝ) * rho + rho) hfull
    have hcount : (s.card : ℝ) / logScale N ≤ rho + 1 / logScale N := by
      have h := (abs_le.mp htotal).2
      dsimp only [s]
      linarith
    have hweighted := mul_le_mul_of_nonneg_left hcount homega
    have hrepdiv := div_le_div_of_nonneg_right hreplace hL.le
    have heq : ((q : ℝ) + 1) * rho = (q : ℝ) * rho + rho := by ring
    change (∫ t in (q : ℝ) * rho..((q : ℝ) + 1) * rho,
      ∫ p, f p ∂(mu t : Measure (Simplex k))) ≤ _
    rw [heq]
    change (∫ t in (q : ℝ) * rho..(q : ℝ) * rho + rho,
      ∫ p, f p ∂(mu t : Measure (Simplex k))) ≤
      (∑ j ∈ s, f (cuts.profile (by omega) j)) / logScale N +
        (2 * omega + M * (P.cellCount : ℝ) * phi) * rho +
          (omega + M + 2 * M * (P.cellCount : ℝ)) / logScale N
    have hreplaceBound :
        (∑ j ∈ s, f (P.rep (P.classify (cuts.profile (by omega) j)))) / logScale N ≤
        (∑ j ∈ s, f (cuts.profile (by omega) j)) / logScale N +
          omega * (rho + 1 / logScale N) := by
      calc
        _ ≤ ((∑ j ∈ s, f (cuts.profile (by omega) j)) + omega * (s.card : ℝ)) /
            logScale N := hrepdiv
        _ = (∑ j ∈ s, f (cuts.profile (by omega) j)) / logScale N +
            omega * ((s.card : ℝ) / logScale N) := by ring
        _ ≤ _ := add_le_add le_rfl hweighted
    have hnorm :
        omega * (rho + 1 / logScale N) + omega * rho +
          M * (1 / logScale N + (P.cellCount : ℝ) * (phi * rho + 2 / logScale N)) =
        (2 * omega + M * (P.cellCount : ℝ) * phi) * rho +
          (omega + M + 2 * M * (P.cellCount : ℝ)) / logScale N := by ring
    dsimp only [s] at hreplaceBound
    linarith [hquad, hnorm]
  have hout := grid_integral_assembly (columnTime N) F g hL hT hrho hM
    (by positivity : 0 ≤ 2 * omega + M * (P.cellCount : ℝ) * phi)
    (by positivity : 0 ≤ omega + M + 2 * M * (P.cellCount : ℝ))
    (fun t => probability_integral_bounds (mu t) f hM hf)
    (fun j => (hf (cuts.profile (by omega) j)).1) ha hab hb hblock
  change (∫ t in a..b, ∫ p, f p ∂(mu t : Measure (Simplex k))) ≤ _ at hout
  have heq : (2 * omega + M * (P.cellCount : ℝ) * phi) * T + 2 * M * rho +
      (omega + M + 2 * M * (P.cellCount : ℝ)) * ((⌊T / rho⌋₊ : ℝ) + 1) / logScale N =
        quadratureError N T rho phi P.cellCount M omega := by
    simp only [quadratureError, Nat.cast_add, Nat.cast_one]
    ring
  calc
    _ ≤ _ := hout
    _ = _ := by
      dsimp only [sampleWindow, timePositions, g]
      rw [← heq]
      ring

end RiffleLowerV2.ProfileTransfer.Compat
