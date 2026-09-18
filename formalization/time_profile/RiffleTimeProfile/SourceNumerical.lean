import RiffleTimeProfile.Crossing
import RiffleTimeProfile.SideMass
import RiffleTimeProfile.AnalyticParameters
import RiffleTimeProfile.IntegratedBounds

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Set

namespace TimeProfile

private theorem prefix_time_le_horizon {N m : ℕ} {T : ℝ}
    (hN : 2 ≤ N) (hT : 0 ≤ T) (hm : m ≤ horizonDepth N T) :
    (m : ℝ) / logScale N ≤ T := by
  apply (div_le_iff₀ (logScale_pos hN)).mpr
  exact (Nat.cast_le.mpr hm).trans
    (Nat.floor_le (mul_nonneg hT (logScale_pos hN).le))

private theorem source_ordered_times {N v n : ℕ} {T r : ℝ}
    (hN : 2 ≤ N) (hT : 0 ≤ T) (hrT : r ≤ T)
    (hvn : v ≤ n) (hnK : n ≤ horizonDepth N T) :
    r ≤ max r ((v : ℝ) / logScale N) ∧
    max r ((v : ℝ) / logScale N) ≤ max r ((n : ℝ) / logScale N) ∧
    max r ((n : ℝ) / logScale N) ≤ T := by
  refine ⟨le_max_left _ _, ?_, max_le hrT (prefix_time_le_horizon hN hT hnK)⟩
  exact max_le_max le_rfl
    (div_le_div_of_nonneg_right (by exact_mod_cast hvn) (logScale_pos hN).le)

/-- The finite representative-cost error uses the actual horizon floor. -/
theorem profile_cost_replacement_horizon {k N R : ℕ} {T : ℝ}
    (p : Fin (horizonDepth N T) → Simplex k)
    (x : Fin (horizonDepth N T) → Fin k) (P : BorelPartition k)
    (timeClass : Fin (horizonDepth N T) → Fin R) (chi C b : ℝ)
    {w v n : ℕ} (hN : 2 ≤ N) (hT : 0 ≤ T) (hchi : 0 < chi) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hwv : w ≤ v) (hvn : v ≤ n)
    (hnK : n ≤ horizonDepth N T) (hlegal : LegalPrefix p x n) :
    cL N p x b w n ≤ cL N p x b w v - profileS N p x P timeClass chi v n -
      profileQ N p x P chi v n + C * chi * T := by
  have hraw := (abs_le.mp (profile_cost_replacement N p x P timeClass chi C b
    hN hchi hC hreg hwv hvn hnK hlegal).2).2
  have htime := prefix_time_le_horizon hN hT
    (show n - v ≤ horizonDepth N T by omega)
  have herror := mul_le_mul_of_nonneg_left htime (mul_nonneg hC hchi.le)
  rw [← mul_div_assoc] at herror
  linarith

/-- The parent-crossing error has its final-column contribution displayed explicitly. -/
theorem profile_parent_crossing_horizon {k N R : ℕ} {T : ℝ}
    (p : Fin (horizonDepth N T) → Simplex k)
    (x : Fin (horizonDepth N T) → Fin k) (P : BorelPartition k)
    (timeClass : Fin (horizonDepth N T) → Fin R) (chi C b F delta : ℝ)
    {w v n : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (hT : 0 ≤ T)
    (hchi : 0 < chi) (hchiK : chi < 1 / (k : ℝ)) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hwv : w ≤ v) (hnK : n ≤ horizonDepth N T)
    (hlegal : LegalPrefix p x n) (hdelta : 0 ≤ delta)
    (hparent : ParentCrossing N p x b w v n F delta) :
    profileS N p x P timeClass chi v n ≤ cL N p x b w v - F +
      (C * chi * T + Real.log (1 / chi) / logScale N) := by
  have hraw := profile_parent_crossing_bound N p x P timeClass chi C b F delta
    hN hk hchi hchiK hC hreg hwv hparent.1 hparent.2.1 hnK hlegal hdelta hparent.2.2
  have htime := prefix_time_le_horizon hN hT
    (show n - 1 - v ≤ horizonDepth N T by omega)
  have herror := mul_le_mul_of_nonneg_left htime (mul_nonneg hC hchi.le)
  rw [← mul_div_assoc] at herror
  linarith

private theorem source_errors_nonneg {k N : ℕ} {T chi C rho phi er eb alpha : ℝ}
    {P : BorelPartition k} (hk : 2 ≤ k) (hN : 2 ≤ N) (hT : 0 ≤ T)
    (hchi : 0 < chi) (hchiK : chi < 1 / (k : ℝ)) (hC : 0 ≤ C)
    (hrho : 0 < rho) (hphi : 0 ≤ phi) (her : 0 ≤ er) (heb : 0 ≤ eb)
    (halpha : 0 ≤ alpha) :
    let A := 4 * Real.log (k : ℝ)
    let E := quadratureError N T rho phi P.cellCount A (C * chi)
    0 ≤ C * chi * T ∧
    0 ≤ C * chi * T + Real.log (1 / chi) / logScale N ∧
    0 ≤ (eb + Real.log (1 / chi) / logScale N) / 2 ∧
    0 ≤ E + A * (er + 1 / logScale N) ∧
    0 ≤ E + A * alpha ∧ 0 ≤ E := by
  have hA : 0 ≤ 4 * Real.log (k : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
  have hL := logScale_pos hN
  have hchiOne : chi ≤ 1 := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    exact hchiK.le.trans ((div_le_one hkpos).mpr hkone)
  have hlog : 0 ≤ Real.log (1 / chi) := Real.log_nonneg ((one_le_div hchi).mpr hchiOne)
  have hE := quadratureError_nonneg (m := P.cellCount) hN hT hrho hphi hA
    (mul_nonneg hC hchi.le)
  dsimp
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity, hE⟩

/-- Literal source data imply the large numerical margin with the explicit finite budget. -/
theorem source_large_margin {k N R : ℕ} {T rho phi chi C r b er eb eta alpha delta : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T) (her : 0 ≤ er) (heb : 0 ≤ eb)
    (heta : 0 < eta) (halpha : 0 ≤ alpha) (hdelta : 0 ≤ delta)
    (hFM : FirstMomentMargin mu r b T eta)
    (x : Fin (horizonDepth N T) → Fin k) (timeClass : Fin (horizonDepth N T) → Fin R)
    {w v n : ℕ} (hwv : w ≤ v) (hvn : v ≤ n) (hnK : n ≤ horizonDepth N T)
    (hlegal : LegalPrefix (cuts.profile (by omega)) x n)
    (hambient : AmbientApproximation N (cuts.profile (by omega)) x w r b er eb)
    (hR : profileR N (cuts.profile (by omega)) x P chi v n ≤ alpha)
    (hcross : Crossings (cuts.profile (by omega)) x w v chi)
    (hbudget :
      let A := 4 * Real.log (k : ℝ)
      let E := quadratureError N T rho phi P.cellCount A (C * chi)
      largeLoss (C * chi * T) ((eb + Real.log (1 / chi) / logScale N) / 2)
        (E + A * (er + 1 / logScale N)) delta (E + A * alpha) E ≤ eta / 2) :
    ∃ F : ℝ, cF N (cuts.profile (by omega)) x w v = (F : WithBot ℝ) ∧
      (StableAt N (cuts.profile (by omega)) x b w n F delta →
        4 * cL N (cuts.profile (by omega)) x b w n - F +
          2 * cE N (cuts.profile (by omega)) n +
          profileH N (cuts.profile (by omega)) x P timeClass chi v n ≤ -eta / 2) := by
  let p := cuts.profile (by omega : 0 < N)
  let A := 4 * Real.log (k : ℝ)
  let E := quadratureError N T rho phi P.cellCount A (C * chi)
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
  have hlegalv : LegalPrefix p x v := fun j hj => hlegal j (lt_of_lt_of_le hj hvn)
  obtain ⟨_, _, _, _, F, hF, hfluc⟩ := cF_lower_bound_of_crossings N p x
    (M := v) hN hchi.1 hwv le_rfl (hvn.trans hnK) hlegalv hcross hambient.2
  refine ⟨F, hF, ?_⟩
  intro hstable
  obtain ⟨heL, _, heF, heBeta, heH, heE⟩ := source_errors_nonneg (P := P)
    hk hN hT hchi.1 hchi.2 hC hrho hphi her heb halpha
  have hmax := source_prefix_max_bound (b := b) cuts hN hk mu P hT hrho hphi hchi hC
    hreg hLike hr0 hrT x hwv (hvn.trans hnK) hlegalv her hambient.1
  have hentropy : ∀ theta ∈ Icc (3 : ℝ) 4,
      profileH N p x P timeClass chi v n ≤ theta * profileS N p x P timeClass chi v n -
        integratedPsi mu theta (max r ((v : ℝ) / logScale N))
          (max r ((n : ℝ) / logScale N)) + (E + A * alpha) := by
    intro theta htheta
    have h := source_entropy_bound cuts hN hk mu P hT hrho hphi hchi hC
      hreg hLike hr0 hrT x timeClass hvn hnK htheta
    have hm := mul_le_mul_of_nonneg_left hR hA
    dsimp only [p, E, A] at hm ⊢
    linarith
  have htail := source_tail_bound cuts hN hk mu P hT hrho hphi hchi hC
    hreg hLike hr0 hrT hnK
  have hord := source_ordered_times hN hT hrT hvn hnK
  have hmargin := (hFM.2.1 _ _ hord.1 hord.2.1 hord.2.2).1
  exact large_numerical_margin heL heF heBeta hdelta heH heE
    (profile_cost_replacement_horizon p x P timeClass chi C b
      hN hT hchi.1 hC hreg hwv hvn hnK hlegal)
    (profileQ_nonneg N p x P chi C v n hN hchi.1 hreg hlegal)
    hstable hfluc (by simpa only [add_assoc] using hmax) hentropy htail hmargin heta hbudget

/-- The small nonsingleton margin uses only the stated parent crossing. -/
theorem source_small_margin {k N R : ℕ} {T rho phi chi C r b er eb eta alpha delta : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T) (her : 0 ≤ er) (heb : 0 ≤ eb)
    (heta : 0 < eta) (halpha : 0 ≤ alpha) (hdelta : 0 ≤ delta)
    (hFM : FirstMomentMargin mu r b T eta)
    (x : Fin (horizonDepth N T) → Fin k) (timeClass : Fin (horizonDepth N T) → Fin R)
    {w v n : ℕ} (hwv : w ≤ v) (hvn : v ≤ n) (hnK : n ≤ horizonDepth N T)
    (hlegal : LegalPrefix (cuts.profile (by omega)) x n)
    (hambient : AmbientApproximation N (cuts.profile (by omega)) x w r b er eb)
    (hR : profileR N (cuts.profile (by omega)) x P chi v n ≤ alpha)
    (hcross : Crossings (cuts.profile (by omega)) x w v chi)
    (hbudget :
      let A := 4 * Real.log (k : ℝ)
      let E := quadratureError N T rho phi P.cellCount A (C * chi)
      smallLoss (E + A * (er + 1 / logScale N))
        ((eb + Real.log (1 / chi) / logScale N) / 2)
        (C * chi * T + Real.log (1 / chi) / logScale N) (E + A * alpha) E ≤ eta / 2) :
    ∃ F : ℝ, cF N (cuts.profile (by omega)) x w v = (F : WithBot ℝ) ∧
      (ParentCrossing N (cuts.profile (by omega)) x b w v n F delta →
        -F + 2 * cE N (cuts.profile (by omega)) n +
          profileH N (cuts.profile (by omega)) x P timeClass chi v n ≤ -eta / 2) := by
  let p := cuts.profile (by omega : 0 < N)
  let A := 4 * Real.log (k : ℝ)
  let E := quadratureError N T rho phi P.cellCount A (C * chi)
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
  have hlegalv : LegalPrefix p x v := fun j hj => hlegal j (lt_of_lt_of_le hj hvn)
  obtain ⟨_, _, _, _, F, hF, hfluc⟩ := cF_lower_bound_of_crossings N p x
    (M := v) hN hchi.1 hwv le_rfl (hvn.trans hnK) hlegalv hcross hambient.2
  refine ⟨F, hF, ?_⟩
  intro hparent
  obtain ⟨_, heS, heF, heBeta, heH, heE⟩ := source_errors_nonneg (P := P)
    hk hN hT hchi.1 hchi.2 hC hrho hphi her heb halpha
  have hmax := source_prefix_max_bound (b := b) cuts hN hk mu P hT hrho hphi hchi hC
    hreg hLike hr0 hrT x hwv (hvn.trans hnK) hlegalv her hambient.1
  have hentropy : ∀ theta ∈ Icc (3 : ℝ) 4,
      profileH N p x P timeClass chi v n ≤ theta * profileS N p x P timeClass chi v n -
        integratedPsi mu theta (max r ((v : ℝ) / logScale N))
          (max r ((n : ℝ) / logScale N)) + (E + A * alpha) := by
    intro theta htheta
    have h := source_entropy_bound cuts hN hk mu P hT hrho hphi hchi hC
      hreg hLike hr0 hrT x timeClass hvn hnK htheta
    have hm := mul_le_mul_of_nonneg_left hR hA
    dsimp only [p, E, A] at hm ⊢
    linarith
  have htail := source_tail_bound cuts hN hk mu P hT hrho hphi hchi hC
    hreg hLike hr0 hrT hnK
  have hord := source_ordered_times hN hT hrT hvn hnK
  have hmargin := (hFM.2.1 _ _ hord.1 hord.2.1 hord.2.2).2
  exact small_numerical_margin heBeta heF heS heH heE
    (profile_parent_crossing_horizon p x P timeClass chi C b F delta
      hN hk hT hchi.1 hchi.2 hC hreg hwv hnK hlegal hdelta hparent)
    hfluc (by simpa only [add_assoc] using hmax) hentropy htail hmargin heta hbudget

/-- The singleton branch has no fluctuation, mass-error or exceptional-profile premise. -/
theorem source_singleton_margin {k N : ℕ} {T rho phi chi C r b er eta : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T) (her : 0 ≤ er) (heta : 0 < eta)
    (hFM : FirstMomentMargin mu r b T eta)
    (x : Fin (horizonDepth N T) → Fin k) {w v : ℕ} (hwv : w ≤ v)
    (hvK : v ≤ horizonDepth N T) (hlegal : LegalPrefix (cuts.profile (by omega)) x v)
    (htime : |(w : ℝ) / logScale N - r| ≤ er)
    (hbudget :
      let A := 4 * Real.log (k : ℝ)
      let E := quadratureError N T rho phi P.cellCount A (C * chi)
      (E + A * (er + 1 / logScale N)) + E ≤ eta / 2) :
    cL N (cuts.profile (by omega)) x b w v + cE N (cuts.profile (by omega)) v ≤
      -eta / 2 := by
  have hA : 0 ≤ 4 * Real.log (k : ℝ) := mul_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
  have hE := quadratureError_nonneg (m := P.cellCount) hN hT hrho hphi hA
    (mul_nonneg hC hchi.1.le)
  have hL := logScale_pos hN
  have heBeta : 0 ≤ quadratureError N T rho phi P.cellCount (4 * Real.log (k : ℝ))
      (C * chi) + (4 * Real.log (k : ℝ)) * (er + 1 / logScale N) := by positivity
  have hmax := source_prefix_max_bound (b := b) cuts hN hk mu P hT hrho hphi hchi hC
    hreg hLike hr0 hrT x hwv hvK hlegal her htime
  have htail := source_tail_bound cuts hN hk mu P hT hrho hphi hchi hC
    hreg hLike hr0 hrT hvK
  have hmargin := hFM.2.2 (max r ((v : ℝ) / logScale N)) (le_max_left _ _)
    (max_le hrT (prefix_time_le_horizon hN hT hvK))
  exact singleton_numerical_margin heBeta hE
    (by simpa only [add_assoc] using hmax) htail hmargin heta hbudget

/-- The terminal source estimate at T excludes fallback without a stability premise. -/
theorem source_no_terminal_fallback {k N : ℕ} {T rho phi chi C r b er eb eta delta : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C) (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T) (her : 0 ≤ er) (heb : 0 ≤ eb)
    (_heta : 0 < eta) (hdelta : 0 < delta) (hFM : FirstMomentMargin mu r b T eta)
    (x : Fin (horizonDepth N T) → Fin k) {w v : ℕ} (hwv : w ≤ v)
    (hvK : v ≤ horizonDepth N T)
    (hlegal : LegalPrefix (cuts.profile (by omega)) x (horizonDepth N T))
    (hambient : AmbientApproximation N (cuts.profile (by omega)) x w r b er eb)
    (hcross : Crossings (cuts.profile (by omega)) x w v chi)
    (hbudget :
      let A := 4 * Real.log (k : ℝ)
      let E := quadratureError N T rho phi P.cellCount A (C * chi)
      (E + A * (er + 1 / logScale N)) +
        2 * ((eb + Real.log (1 / chi) / logScale N) / 2) ≤ eta) :
    ∃ F : ℝ, cF N (cuts.profile (by omega)) x w v = (F : WithBot ℝ) ∧
      cL N (cuts.profile (by omega)) x b w (horizonDepth N T) - F < delta := by
  let p := cuts.profile (by omega : 0 < N)
  obtain ⟨_, _, _, _, F, hF, hfluc⟩ := cF_lower_bound_of_crossings N p x
    (M := horizonDepth N T) hN hchi.1 hwv hvK le_rfl hlegal hcross hambient.2
  refine ⟨F, hF, ?_⟩
  obtain ⟨_, _, heF, heBeta, _, _⟩ := source_errors_nonneg (P := P) (alpha := 0)
    hk hN hT hchi.1 hchi.2 hC hrho hphi her heb le_rfl
  have hmax := source_terminal_max_bound (b := b) cuts hN hk mu P hT hrho hphi hchi hC
    hreg hLike hr0 hrT x (hwv.trans hvK) hlegal her hambient.1
  apply no_terminal_fallback heBeta heF _ hfluc hbudget hdelta
  have hterminal := hFM.1
  change cL N (cuts.profile (by omega)) x b w (horizonDepth N T) ≤ _
  linarith

/-- C06 and C07 composed: the thresholds precede all source data, and all numerical
budgets are discharged by the quantified choices. Each branch retains its own hypotheses. -/
theorem exists_uniform_source_margins {k : ℕ} (hk : 2 ≤ k)
    {T eta epsilon : ℝ} (hT : 0 ≤ T) (heta : 0 < eta)
    (hepsilon : 0 < epsilon) (hchoice : epsilon ≤ eta / 28) :
    ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 ≤ 1 / (k : ℝ) ∧
      ∀ chi : ℝ, 0 < chi → chi < chi0 →
        ∃ P : BorelPartition k, P.IsRegular chi 1 ∧
          ∃ rho0 : ℝ, 0 < rho0 ∧
            ∀ rho : ℝ, 0 < rho → rho < rho0 →
              ∃ phi0 : ℝ, 0 < phi0 ∧
                ∀ phi : ℝ, 0 ≤ phi → phi ≤ phi0 →
                  ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
                    ∀ N : ℕ, ∀ hNN : N0 ≤ N,
                      ∀ (cuts : Cuts k N (horizonDepth N T)) (mu : TimeLaw k),
                        AlmostLike cuts (by omega) mu P T rho phi →
                        ∀ r b : ℝ, 0 ≤ r → r ≤ T → FirstMomentMargin mu r b T eta →
                          (∀ er : ℝ, 0 ≤ er → (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4 →
                            ∀ (x : Fin (horizonDepth N T) → Fin k) (w v : ℕ),
                              w ≤ v → v ≤ horizonDepth N T →
                              LegalPrefix (cuts.profile (by omega)) x v →
                              |(w : ℝ) / logScale N - r| ≤ er →
                              cL N (cuts.profile (by omega)) x b w v +
                                cE N (cuts.profile (by omega)) v ≤ -eta / 2) ∧
                          (∀ er eb delta : ℝ, 0 ≤ er → 0 ≤ eb →
                            (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4 → eb ≤ epsilon →
                            delta ∈ Icc (0 : ℝ) epsilon →
                            ∀ (R : ℕ) (timeClass : Fin (horizonDepth N T) → Fin R)
                              (x : Fin (horizonDepth N T) → Fin k) (w v n : ℕ),
                              w ≤ v → v ≤ n → n ≤ horizonDepth N T →
                              LegalPrefix (cuts.profile (by omega)) x n →
                              AmbientApproximation N (cuts.profile (by omega)) x w r b er eb →
                              profileR N (cuts.profile (by omega)) x P chi v n ≤
                                exceptionalAllowance chi →
                              Crossings (cuts.profile (by omega)) x w v chi →
                              ∃ F : ℝ, cF N (cuts.profile (by omega)) x w v = (F : WithBot ℝ) ∧
                                (StableAt N (cuts.profile (by omega)) x b w n F delta →
                                  4 * cL N (cuts.profile (by omega)) x b w n - F +
                                    2 * cE N (cuts.profile (by omega)) n +
                                    profileH N (cuts.profile (by omega)) x P timeClass chi v n ≤
                                      -eta / 2) ∧
                                (ParentCrossing N (cuts.profile (by omega)) x b w v n F delta →
                                  -F + 2 * cE N (cuts.profile (by omega)) n +
                                    profileH N (cuts.profile (by omega)) x P timeClass chi v n ≤
                                      -eta / 2)) ∧
                          (∀ er eb delta : ℝ, 0 ≤ er → 0 ≤ eb →
                            (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4 → eb ≤ epsilon →
                            0 < delta →
                            ∀ (x : Fin (horizonDepth N T) → Fin k) (w v : ℕ),
                              w ≤ v → v ≤ horizonDepth N T →
                              LegalPrefix (cuts.profile (by omega)) x (horizonDepth N T) →
                              AmbientApproximation N (cuts.profile (by omega)) x w r b er eb →
                              Crossings (cuts.profile (by omega)) x w v chi →
                              ∃ F : ℝ, cF N (cuts.profile (by omega)) x w v = (F : WithBot ℝ) ∧
                                cL N (cuts.profile (by omega)) x b w (horizonDepth N T) - F <
                                  delta) := by
  obtain ⟨chi0, hchi0, hchi0K, hchiSmall⟩ := exists_source_parameter_thresholds hk hT hepsilon
  refine ⟨chi0, hchi0, hchi0K, ?_⟩
  intro chi hchi hchiSmall'
  have hchiK : chi < 1 / (k : ℝ) := hchiSmall'.trans_le hchi0K
  obtain ⟨hchiBudget, hbadBudget, hpartition⟩ := hchiSmall chi hchi hchiSmall'
  obtain ⟨P, hreg⟩ := exists_regular_partition hk hchi hchiK
  obtain ⟨rho0, hrho0, hrhoSmall⟩ := hpartition P.cellCount
  refine ⟨P, hreg, rho0, hrho0, ?_⟩
  intro rho hrho hrhoSmall'
  obtain ⟨hrhoBudget, phi0, hphi0, hphiSmall⟩ := hrhoSmall rho hrho hrhoSmall'
  refine ⟨phi0, hphi0, ?_⟩
  intro phi hphi hphiSmall'
  obtain ⟨hphiBudget, N0, hN0, hNlarge⟩ := hphiSmall phi hphi hphiSmall'
  refine ⟨N0, hN0, ?_⟩
  intro N hNN
  have hN : 2 ≤ N := hN0.trans hNN
  have hNbudget := hNlarge N hNN
  have hbudgets : ∀ er eb delta : ℝ, 0 ≤ er → 0 ≤ eb →
      (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4 → eb ≤ epsilon →
      delta ∈ Icc (0 : ℝ) epsilon →
      let A := 4 * Real.log (k : ℝ)
      let E := quadratureError N T rho phi P.cellCount A chi
      largeLoss (chi * T) ((eb + Real.log (1 / chi) / logScale N) / 2)
          (E + A * (er + 1 / logScale N)) delta (E + A * exceptionalAllowance chi) E ≤
          eta / 2 ∧
        smallLoss (E + A * (er + 1 / logScale N))
          ((eb + Real.log (1 / chi) / logScale N) / 2)
          (chi * T + Real.log (1 / chi) / logScale N) (E + A * exceptionalAllowance chi) E ≤
          eta / 2 ∧
        (E + A * (er + 1 / logScale N)) + E ≤ eta / 2 ∧
        (E + A * (er + 1 / logScale N)) +
          2 * ((eb + Real.log (1 / chi) / logScale N) / 2) ≤ eta := by
    intro er eb delta her heb herBudget hebBudget hdelta
    obtain ⟨heL, heS, heF, heBeta, heH, heE⟩ := source_error_bounds hk hN hT
      hchi hchiK hrho hphi her heb hepsilon hchiBudget hbadBudget hrhoBudget
      hphiBudget herBudget hebBudget hNbudget
    exact numerical_budgets_of_common_bounds heL heS heF heBeta heH heE hdelta hchoice
  intro cuts mu hLike r b hr0 hrT hFM
  refine ⟨?_, ?_, ?_⟩
  · intro er her herBudget x w v hwv hvK hlegal htime
    have hb := hbudgets er 0 0 her le_rfl herBudget hepsilon.le ⟨le_rfl, hepsilon.le⟩
    apply source_singleton_margin cuts hN hk mu P hT hrho hphi ⟨hchi, hchiK⟩
      (by norm_num) hreg hLike hr0 hrT her heta hFM x hwv hvK hlegal htime
    simpa only [one_mul] using hb.2.2.1
  · intro er eb delta her heb herBudget hebBudget hdelta R timeClass x w v n
      hwv hvn hnK hlegal hambient hR hcross
    have hb := hbudgets er eb delta her heb herBudget hebBudget hdelta
    obtain ⟨F, hF, hlarge⟩ := source_large_margin cuts hN hk mu P hT hrho hphi
      ⟨hchi, hchiK⟩ (by norm_num) hreg hLike hr0 hrT her heb heta
      (exceptionalAllowance_nonneg chi) hdelta.1 hFM x timeClass hwv hvn hnK hlegal
      hambient hR hcross (by simpa only [one_mul] using hb.1)
    obtain ⟨G, hG, hsmall⟩ := source_small_margin cuts hN hk mu P hT hrho hphi
      ⟨hchi, hchiK⟩ (by norm_num) hreg hLike hr0 hrT her heb heta
      (exceptionalAllowance_nonneg chi) hdelta.1 hFM x timeClass hwv hvn hnK hlegal
      hambient hR hcross (by simpa only [one_mul] using hb.2.1)
    have hFG : F = G := by exact_mod_cast hF.symm.trans hG
    subst G
    exact ⟨F, hF, hlarge, hsmall⟩
  · intro er eb delta her heb herBudget hebBudget hdelta x w v hwv hvK hlegal hambient hcross
    have hb := hbudgets er eb 0 her heb herBudget hebBudget ⟨le_rfl, hepsilon.le⟩
    apply source_no_terminal_fallback cuts hN hk mu P hT hrho hphi ⟨hchi, hchiK⟩
      (by norm_num) hreg hLike hr0 hrT her heb heta hdelta hFM x hwv hvK hlegal hambient hcross
    simpa only [one_mul] using hb.2.2.2

end TimeProfile
