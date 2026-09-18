import RiffleTimeProfile.GridQuadrature
import RiffleTimeProfile.DigitEstimates
import RiffleTimeProfile.Source
import RiffleTimeProfile.AnalyticParameters

/-! C05: integrated bounds for the literal source data. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace TimeProfile

private theorem positions_iff_time {N K w v : ℕ} (hN : 2 ≤ N) (j : Fin K) :
    j ∈ positions K w v ↔
      (w : ℝ) / logScale N < columnTime N j ∧
        columnTime N j ≤ (v : ℝ) / logScale N := by
  have hL := logScale_pos hN
  simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and, columnTime,
    div_lt_div_iff_of_pos_right hL, div_le_div_iff_of_pos_right hL]
  constructor
  · rintro ⟨hw, hv⟩
    exact ⟨by exact_mod_cast (show w < j.val + 1 by omega),
      by exact_mod_cast (show j.val + 1 ≤ v by omega)⟩
  · rintro ⟨hw, hv⟩
    have hw' : w < j.val + 1 := by exact_mod_cast hw
    have hv' : j.val + 1 ≤ v := by exact_mod_cast hv
    omega

private theorem depth_time_le {N v : ℕ} {T : ℝ} (hN : 2 ≤ N) (hT : 0 ≤ T)
    (hv : v ≤ horizonDepth N T) : (v : ℝ) / logScale N ≤ T := by
  have hdiv : (v : ℝ) / logScale N ≤ (horizonDepth N T : ℝ) / logScale N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hv) (logScale_pos hN).le
  exact hdiv.trans (sub_nonneg.mp (horizonDepth_error hN hT).1)

private theorem clamped_positions_subset {N K v n : ℕ} {r : ℝ} (hN : 2 ≤ N) :
    timePositions N K (max r ((v : ℝ) / logScale N))
      (max r ((n : ℝ) / logScale N)) ⊆ positions K v n := by
  intro j hj
  have ht := mem_timePositions.mp hj
  apply (positions_iff_time hN j).mpr
  refine ⟨(le_max_right _ _).trans_lt ht.1, ?_⟩
  rcases le_max_iff.mp ht.2 with hr | hn
  · exact False.elim ((not_lt_of_ge hr) ((le_max_left _ _).trans_lt ht.1))
  · exact hn

private theorem maxCost_le_digitCost {k : ℕ} (p : Simplex k) (l : Fin k)
    (hpos : 0 < prob p l) : maxCost p ≤ digitCost (prob p l) := by
  apply Real.log_le_log (one_div_pos.mpr (pileMax_pos p))
  exact one_div_le_one_div_of_le hpos (prob_le_pileMax p l)

private theorem shifted_prefix_sum_le {N w v : ℕ} {T r er M : ℝ}
    (hN : 2 ≤ N) (hT : 0 ≤ T) (hr : 0 ≤ r) (her : 0 ≤ er) (hM : 0 ≤ M)
    (hwv : w ≤ v) (hvK : v ≤ horizonDepth N T)
    (htime : |(w : ℝ) / logScale N - r| ≤ er)
    (s : Finset (Fin (horizonDepth N T)))
    (hs : ∀ j ∈ s, r < columnTime N j ∧ j.val < v)
    (f g : Fin (horizonDepth N T) → ℝ)
    (hf : ∀ j, 0 ≤ f j ∧ f j ≤ M)
    (hfg : ∀ j ∈ positions (horizonDepth N T) w v, f j ≤ g j) :
    (∑ j ∈ s, f j) / logScale N ≤
      (∑ j ∈ positions (horizonDepth N T) w v, g j) / logScale N +
        M * (er + 1 / logScale N) := by
  classical
  let q := positions (horizonDepth N T) w v
  let birth := timePositions N (horizonDepth N T)
    (min r ((w : ℝ) / logScale N)) ((w : ℝ) / logScale N)
  have hL := logScale_pos hN
  have hw0 : 0 ≤ (w : ℝ) / logScale N := div_nonneg (Nat.cast_nonneg _) hL.le
  have hwT := depth_time_le hN hT (hwv.trans hvK)
  have hsubset : s \ q ⊆ birth := by
    intro j hj
    have hs' := hs j (Finset.mem_sdiff.mp hj).1
    have hnq := (Finset.mem_sdiff.mp hj).2
    have hjw : j.val < w := by
      dsimp only [q] at hnq
      simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and] at hnq
      omega
    apply mem_timePositions.mpr
    refine ⟨(min_le_left _ _).trans_lt hs'.1, ?_⟩
    have hp : j ∈ positions (horizonDepth N T) 0 w := by
      simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Nat.zero_le _, hjw⟩
    exact ((positions_iff_time hN j).mp hp).2
  have hcount : (birth.card : ℝ) / logScale N ≤ er + 1 / logScale N := by
    have he := timePositions_count_error hN (le_min hr hw0)
      (min_le_right r ((w : ℝ) / logScale N)) hwT
    have hlength : (w : ℝ) / logScale N - min r ((w : ℝ) / logScale N) ≤ er := by
      by_cases hrw : r ≤ (w : ℝ) / logScale N
      · rw [min_eq_left hrw]
        exact (abs_le.mp htime).2
      · rw [min_eq_right (le_of_not_ge hrw), sub_self]
        exact her
    dsimp only [birth]
    linarith [(abs_le.mp he).2]
  have hinter : ∑ j ∈ s ∩ q, f j ≤ ∑ j ∈ q, g j := by
    calc
      ∑ j ∈ s ∩ q, f j ≤ ∑ j ∈ q, f j :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun j _ _ => (hf j).1)
      _ ≤ ∑ j ∈ q, g j := Finset.sum_le_sum (fun j hj => hfg j hj)
  have hdiff : ∑ j ∈ s \ q, f j ≤ (birth.card : ℝ) * M := by
    calc
      ∑ j ∈ s \ q, f j ≤ ∑ _j ∈ s \ q, M :=
        Finset.sum_le_sum (fun j _ => (hf j).2)
      _ = ((s \ q).card : ℝ) * M := by simp
      _ ≤ (birth.card : ℝ) * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_mono hsubset) hM
  have hsplit := Finset.sum_inter_add_sum_sdiff s q f
  have hsum : ∑ j ∈ s, f j ≤ (∑ j ∈ q, g j) + (birth.card : ℝ) * M := by
    linarith
  calc
    (∑ j ∈ s, f j) / logScale N ≤
        ((∑ j ∈ q, g j) + (birth.card : ℝ) * M) / logScale N :=
      div_le_div_of_nonneg_right hsum hL.le
    _ = (∑ j ∈ q, g j) / logScale N + M * ((birth.card : ℝ) / logScale N) := by ring
    _ ≤ (∑ j ∈ q, g j) / logScale N + M * (er + 1 / logScale N) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hM)

theorem source_tail_bound {k N : ℕ} {T rho phi chi C r : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T) {n : ℕ} (hnK : n ≤ horizonDepth N T) :
    cE N (cuts.profile (by omega)) n ≤
      -integratedPsi mu 2 (max r ((n : ℝ) / logScale N)) T +
        quadratureError N T rho phi P.cellCount (4 * Real.log (k : ℝ)) (C * chi) := by
  have hL := logScale_pos hN
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hA : 0 ≤ 4 * Real.log (k : ℝ) := by positivity
  have hu : max r ((n : ℝ) / logScale N) ≤ T :=
    max_le hrT (depth_time_le hN hT hnK)
  have hquad := one_sided_quadrature cuts hN mu P (fun p => psi p 2)
    hT hrho hphi hA (mul_nonneg hC hchi.1.le)
    (fun p => psi_bounds hk p (by norm_num))
    (fun p => hreg.psi_rep_error p (by norm_num)) hLike
    (hr0.trans (le_max_left _ _)) hu le_rfl
  have hsub : timePositions N (horizonDepth N T)
      (max r ((n : ℝ) / logScale N)) T ⊆ positions (horizonDepth N T) n (horizonDepth N T) := by
    intro j hj
    have ht := mem_timePositions.mp hj
    apply (positions_iff_time hN j).mpr
    refine ⟨(le_max_right _ _).trans_lt ht.1, ?_⟩
    simp only [columnTime, div_le_div_iff_of_pos_right hL]
    exact_mod_cast (show j.val + 1 ≤ horizonDepth N T by omega)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _ => (psi_bounds hk (cuts.profile (by omega) j) (by norm_num : (2 : ℝ) ∈ Icc 2 4)).1)
  have hdiv := div_le_div_of_nonneg_right hsum hL.le
  change integratedPsi mu 2 (max r ((n : ℝ) / logScale N)) T ≤ _ at hquad
  unfold cE
  rw [neg_div]
  linarith

theorem source_entropy_bound {k N R : ℕ} {T rho phi chi C r : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T)
    (x : Fin (horizonDepth N T) → Fin k) (timeClass : Fin (horizonDepth N T) → Fin R)
    {v n : ℕ} (hvn : v ≤ n) (hnK : n ≤ horizonDepth N T)
    {theta : ℝ} (htheta : theta ∈ Icc (3 : ℝ) 4) :
    profileH N (cuts.profile (by omega)) x P timeClass chi v n ≤
      theta * profileS N (cuts.profile (by omega)) x P timeClass chi v n -
        integratedPsi mu theta (max r ((v : ℝ) / logScale N))
          (max r ((n : ℝ) / logScale N)) +
        quadratureError N T rho phi P.cellCount (4 * Real.log (k : ℝ)) (C * chi) +
        (4 * Real.log (k : ℝ)) * profileR N (cuts.profile (by omega)) x P chi v n := by
  have hL := logScale_pos hN
  have htheta' : theta ∈ Icc (2 : ℝ) 4 := ⟨by linarith [htheta.1], htheta.2⟩
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hA : 0 ≤ 4 * Real.log (k : ℝ) := by positivity
  have hsu : max r ((v : ℝ) / logScale N) ≤ max r ((n : ℝ) / logScale N) :=
    max_le_max le_rfl (div_le_div_of_nonneg_right (by exact_mod_cast hvn) hL.le)
  have huT : max r ((n : ℝ) / logScale N) ≤ T :=
    max_le hrT (depth_time_le hN hT hnK)
  have hquad := one_sided_quadrature_representative cuts hN mu P (fun p => psi p theta)
    hT hrho hphi hA (mul_nonneg hC hchi.1.le)
    (fun p => psi_bounds hk p htheta')
    (fun p => hreg.psi_rep_error p htheta') hLike
    (hr0.trans (le_max_left _ _)) hsu huT
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (clamped_positions_subset (v := v) (n := n) (r := r) hN)
    (fun j _ _ => (psi_bounds hk (P.rep (P.classify (cuts.profile (by omega) j))) htheta').1)
  have hdiv := div_le_div_of_nonneg_right hsum hL.le
  have hentropy := profile_entropy_bound N (cuts.profile (by omega)) x P timeClass chi v n
    hN hchi.1 htheta
  have hbad := (exceptional_psi_error N (cuts.profile (by omega)) x P timeClass chi v n
    hk hN htheta').2
  change integratedPsi mu theta (max r ((v : ℝ) / logScale N))
    (max r ((n : ℝ) / logScale N)) ≤ _ at hquad
  linarith

theorem source_prefix_max_bound {k N : ℕ} {T rho phi chi C r b er : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T) (x : Fin (horizonDepth N T) → Fin k)
    {w v : ℕ} (hwv : w ≤ v) (hvK : v ≤ horizonDepth N T)
    (hlegal : LegalPrefix (cuts.profile (by omega)) x v)
    (her : 0 ≤ er) (htime : |(w : ℝ) / logScale N - r| ≤ er) :
    cL N (cuts.profile (by omega)) x b w v ≤
      localBeta mu r b (max r ((v : ℝ) / logScale N)) +
        quadratureError N T rho phi P.cellCount (4 * Real.log (k : ℝ)) (C * chi) +
        (4 * Real.log (k : ℝ)) * (er + 1 / logScale N) := by
  have hL := logScale_pos hN
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hA : 0 ≤ 4 * Real.log (k : ℝ) := by positivity
  have hf : ∀ p : Simplex k, 0 ≤ maxCost p ∧ maxCost p ≤ 4 * Real.log (k : ℝ) := by
    intro p
    exact ⟨(maxCost_bounds hk p).1, by linarith [(maxCost_bounds hk p).2]⟩
  have hquad := one_sided_quadrature cuts hN mu P maxCost hT hrho hphi
    hA (mul_nonneg hC hchi.1.le) hf hreg.maxCost_rep_error hLike hr0
    (le_max_left _ _) (max_le hrT (depth_time_le hN hT hvK))
  have hs : ∀ j ∈ timePositions N (horizonDepth N T) r
      (max r ((v : ℝ) / logScale N)), r < columnTime N j ∧ j.val < v := by
    intro j hj
    have ht := mem_timePositions.mp hj
    refine ⟨ht.1, ?_⟩
    rcases le_max_iff.mp ht.2 with htr | htv
    · exact False.elim ((not_lt_of_ge htr) ht.1)
    · have hjv : (j.val : ℝ) + 1 ≤ (v : ℝ) :=
        (div_le_div_iff_of_pos_right hL).mp htv
      have hjv' : j.val + 1 ≤ v := by exact_mod_cast hjv
      omega
  have hshift := shifted_prefix_sum_le hN hT hr0 her hA hwv hvK htime
    (timePositions N (horizonDepth N T) r (max r ((v : ℝ) / logScale N))) hs
    (fun j => maxCost (cuts.profile (by omega) j))
    (fun j => digitCost (prob (cuts.profile (by omega) j) (x j)))
    (fun j => hf (cuts.profile (by omega) j))
    (fun j hj => maxCost_le_digitCost _ _ (hlegal j (Finset.mem_filter.mp hj).2.2))
  change integratedMaxCost mu r (max r ((v : ℝ) / logScale N)) ≤ _ at hquad
  unfold cL localBeta
  linarith

theorem source_terminal_max_bound {k N : ℕ} {T rho phi chi C r b er : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T) (x : Fin (horizonDepth N T) → Fin k)
    {w : ℕ} (hwK : w ≤ horizonDepth N T)
    (hlegal : LegalPrefix (cuts.profile (by omega)) x (horizonDepth N T))
    (her : 0 ≤ er) (htime : |(w : ℝ) / logScale N - r| ≤ er) :
    cL N (cuts.profile (by omega)) x b w (horizonDepth N T) ≤
      localBeta mu r b T +
        quadratureError N T rho phi P.cellCount (4 * Real.log (k : ℝ)) (C * chi) +
        (4 * Real.log (k : ℝ)) * (er + 1 / logScale N) := by
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hA : 0 ≤ 4 * Real.log (k : ℝ) := by positivity
  have hf : ∀ p : Simplex k, 0 ≤ maxCost p ∧ maxCost p ≤ 4 * Real.log (k : ℝ) := by
    intro p
    exact ⟨(maxCost_bounds hk p).1, by linarith [(maxCost_bounds hk p).2]⟩
  have hquad := one_sided_quadrature cuts hN mu P maxCost hT hrho hphi
    hA (mul_nonneg hC hchi.1.le) hf hreg.maxCost_rep_error hLike hr0 hrT le_rfl
  have hs : ∀ j ∈ timePositions N (horizonDepth N T) r T,
      r < columnTime N j ∧ j.val < horizonDepth N T := by
    intro j hj
    exact ⟨(mem_timePositions.mp hj).1, j.isLt⟩
  have hshift := shifted_prefix_sum_le hN hT hr0 her hA hwK le_rfl htime
    (timePositions N (horizonDepth N T) r T) hs
    (fun j => maxCost (cuts.profile (by omega) j))
    (fun j => digitCost (prob (cuts.profile (by omega) j) (x j)))
    (fun j => hf (cuts.profile (by omega) j))
    (fun j hj => maxCost_le_digitCost _ _ (hlegal j (Finset.mem_filter.mp hj).2.2))
  change integratedMaxCost mu r T ≤ _ at hquad
  unfold cL localBeta
  linarith

end TimeProfile
