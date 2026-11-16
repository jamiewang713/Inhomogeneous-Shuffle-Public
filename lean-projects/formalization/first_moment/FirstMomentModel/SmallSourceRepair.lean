import RiffleTimeProfile.SourceNumerical

namespace InhomogeneousShuffle.FirstMoment.Model

noncomputable section
open TimeProfile Set

theorem small_coarse_numerical_core
    {Lv F E H S beta Dtail theta eBeta eF eS eH eE : ℝ}
    {B : ℝ → ℝ}
    (htheta : theta ∈ Icc (3 : ℝ) 4)
    (heBeta : 0 ≤ eBeta) (heF : 0 ≤ eF) (heS : 0 ≤ eS)
    (heH : 0 ≤ eH) (heE : 0 ≤ eE)
    (hS : 0 ≤ S)
    (hparent : S ≤ Lv - F + eS)
    (hfluc : Lv / 2 - eF ≤ F)
    (hmax : Lv ≤ beta + eBeta)
    (hentropy : H ≤ theta * S - B theta + eH)
    (htail : E ≤ -Dtail + eE) :
    H + 2 * E ≤ largeObjective beta B Dtail theta +
      ((7 / 2 : ℝ) * eBeta + 7 * eF + 7 * eS + eH + 2 * eE) := by
  have hbound : S ≤ beta / 2 + (eBeta / 2 + eF + eS) := by linarith
  have hmult := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ theta + 3 by linarith [htheta.1])
  have herror := mul_nonneg (show 0 ≤ 4 - theta by linarith [htheta.2])
    (show 0 ≤ eBeta / 2 + eF + eS by positivity)
  unfold largeObjective
  nlinarith

theorem small_coarse_numerical_infimum
    {Lv F E H S beta Dtail eBeta eF eS eH eE : ℝ}
    {B : ℝ → ℝ}
    (heBeta : 0 ≤ eBeta) (heF : 0 ≤ eF) (heS : 0 ≤ eS)
    (heH : 0 ≤ eH) (heE : 0 ≤ eE)
    (hS : 0 ≤ S)
    (hparent : S ≤ Lv - F + eS)
    (hfluc : Lv / 2 - eF ≤ F)
    (hmax : Lv ≤ beta + eBeta)
    (hentropy : ∀ theta ∈ Icc (3 : ℝ) 4,
      H ≤ theta * S - B theta + eH)
    (htail : E ≤ -Dtail + eE) :
    H + 2 * E ≤
      sInf (largeObjective beta B Dtail '' Icc (3 : ℝ) 4) +
        ((7 / 2 : ℝ) * eBeta + 7 * eF + 7 * eS + eH + 2 * eE) := by
  apply numerical_le_infimum_add
  intro theta htheta
  exact small_coarse_numerical_core htheta heBeta heF heS heH heE hS
    hparent hfluc hmax (hentropy theta htheta) htail

theorem source_small_coarse_margin
    {k N R : ℕ} {T rho phi chi C r b er eb eta alpha delta : ℝ}
    (cuts : Cuts k N (horizonDepth N T)) (hN : 2 ≤ N) (hk : 2 ≤ k)
    (mu : TimeLaw k) (P : BorelPartition k) (hT : 0 ≤ T) (hrho : 0 < rho)
    (hphi : 0 ≤ phi) (hchi : chi ∈ Ioo (0 : ℝ) (1 / (k : ℝ))) (hC : 0 ≤ C)
    (hreg : P.IsRegular chi C)
    (hLike : AlmostLike cuts (by omega) mu P T rho phi)
    (hr0 : 0 ≤ r) (hrT : r ≤ T) (her : 0 ≤ er) (heb : 0 ≤ eb)
    (heta : 0 < eta) (halpha : 0 ≤ alpha) (hdelta : 0 ≤ delta)
    (hFM : FirstMomentMargin mu r b T eta)
    (x : Fin (horizonDepth N T) → Fin k)
    (timeClass : Fin (horizonDepth N T) → Fin R)
    {w v n : ℕ} (hwv : w ≤ v) (hvn : v ≤ n) (hnK : n ≤ horizonDepth N T)
    (hlegal : LegalPrefix (cuts.profile (by omega)) x n)
    (hambient : AmbientApproximation N (cuts.profile (by omega)) x w r b er eb)
    (hR : profileR N (cuts.profile (by omega)) x P chi v n ≤ alpha)
    (hcross : Crossings (cuts.profile (by omega)) x w v chi)
    (hbudget :
      let A := 4 * Real.log (k : ℝ)
      let Qerr := quadratureError N T rho phi P.cellCount A (C * chi)
      (7 / 2 : ℝ) * (Qerr + A * (er + 1 / logScale N)) +
        7 * ((eb + Real.log (1 / chi) / logScale N) / 2) +
        7 * (C * chi * T + Real.log (1 / chi) / logScale N) +
        (Qerr + A * alpha) + 2 * Qerr + 8 * delta + 4 * eb ≤ 3 * eta / 4) :
    ∃ F : ℝ, cF N (cuts.profile (by omega)) x w v = (F : WithBot ℝ) ∧
      (ParentCrossing N (cuts.profile (by omega)) x b w v n F delta →
        profileH N (cuts.profile (by omega)) x P timeClass chi v n +
          2 * cE N (cuts.profile (by omega)) n + 8 * delta + 4 * eb ≤ -eta / 4) := by
  let p := cuts.profile (by omega : 0 < N)
  let A := 4 * Real.log (k : ℝ)
  let Qerr := quadratureError N T rho phi P.cellCount A (C * chi)
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
  have hL := logScale_pos hN
  have hchiOne : chi ≤ 1 := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    exact hchi.2.le.trans ((div_le_one hkpos).mpr hkone)
  have hlog : 0 ≤ Real.log (1 / chi) :=
    Real.log_nonneg ((one_le_div hchi.1).mpr hchiOne)
  have hQerr : 0 ≤ Qerr := quadratureError_nonneg (m := P.cellCount)
    hN hT hrho hphi hA (mul_nonneg hC hchi.1.le)
  have heBeta : 0 ≤ Qerr + A * (er + 1 / logScale N) := by positivity
  have heF : 0 ≤ (eb + Real.log (1 / chi) / logScale N) / 2 := by positivity
  have heS : 0 ≤ C * chi * T + Real.log (1 / chi) / logScale N := by
    exact add_nonneg (mul_nonneg (mul_nonneg hC hchi.1.le) hT) (div_nonneg hlog hL.le)
  have heH : 0 ≤ Qerr + A * alpha := add_nonneg hQerr (mul_nonneg hA halpha)
  have hlegalv : LegalPrefix p x v := fun j hj => hlegal j (lt_of_lt_of_le hj hvn)
  obtain ⟨_, _, _, _, F, hF, hfluc⟩ := cF_lower_bound_of_crossings N p x
    (M := v) hN hchi.1 hwv le_rfl (hvn.trans hnK) hlegalv hcross hambient.2
  refine ⟨F, hF, ?_⟩
  intro hparent
  have hmax := source_prefix_max_bound (b := b) cuts hN hk mu P hT hrho hphi hchi hC
    hreg hLike hr0 hrT x hwv (hvn.trans hnK) hlegalv her hambient.1
  have hentropy : ∀ theta ∈ Icc (3 : ℝ) 4,
      profileH N p x P timeClass chi v n ≤ theta * profileS N p x P timeClass chi v n -
        integratedPsi mu theta (max r ((v : ℝ) / logScale N))
          (max r ((n : ℝ) / logScale N)) + (Qerr + A * alpha) := by
    intro theta htheta
    have h := source_entropy_bound cuts hN hk mu P hT hrho hphi hchi hC
      hreg hLike hr0 hrT x timeClass hvn hnK htheta
    have hm := mul_le_mul_of_nonneg_left hR hA
    dsimp only [p, Qerr, A] at hm ⊢
    linarith
  have htail := source_tail_bound cuts hN hk mu P hT hrho hphi hchi hC
    hreg hLike hr0 hrT hnK
  have htime : (n : ℝ) / logScale N ≤ T := by
    apply (div_le_iff₀ hL).mpr
    exact (Nat.cast_le.mpr hnK).trans (Nat.floor_le (mul_nonneg hT hL.le))
  have hsu : max r ((v : ℝ) / logScale N) ≤ max r ((n : ℝ) / logScale N) :=
    max_le_max le_rfl (div_le_div_of_nonneg_right (by exact_mod_cast hvn) hL.le)
  have huT : max r ((n : ℝ) / logScale N) ≤ T := max_le hrT htime
  have hmargin := (hFM.2.1 _ _ (le_max_left _ _) hsu huT).1
  have hi := small_coarse_numerical_infimum heBeta heF heS heH hQerr
    (profileS_nonneg N p x P timeClass chi C v n hN hchi.1 hreg hlegal)
    (profile_parent_crossing_horizon p x P timeClass chi C b F delta
      hN hk hT hchi.1 hchi.2 hC hreg hwv hnK hlegal hdelta hparent)
    hfluc (by simpa only [add_assoc] using hmax) hentropy htail
  change sInf (largeObjective (localBeta mu r b (max r ((v : ℝ) / logScale N)))
    (fun theta => integratedPsi mu theta (max r ((v : ℝ) / logScale N))
      (max r ((n : ℝ) / logScale N)))
    (integratedPsi mu 2 (max r ((n : ℝ) / logScale N)) T) '' Icc (3 : ℝ) 4) ≤ -eta at hmargin
  dsimp only [p, Qerr, A] at hi
  dsimp only at hbudget
  linarith

theorem exists_uniform_source_margins_with_small_coarse
    {k : ℕ} (hk : 2 ≤ k)
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
                                      -eta / 2) ∧
                                (ParentCrossing N (cuts.profile (by omega)) x b w v n F delta →
                                  profileH N (cuts.profile (by omega)) x P timeClass chi v n +
                                    2 * cE N (cuts.profile (by omega)) n +
                                    8 * delta + 4 * eb ≤ -eta / 4)) ∧
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
  have hrepairBudget : ∀ er eb delta : ℝ, 0 ≤ er → 0 ≤ eb →
      (4 * Real.log (k : ℝ)) * er ≤ epsilon / 4 → eb ≤ epsilon →
      delta ∈ Icc (0 : ℝ) epsilon →
      let A := 4 * Real.log (k : ℝ)
      let Qerr := quadratureError N T rho phi P.cellCount A chi
      (7 / 2 : ℝ) * (Qerr + A * (er + 1 / logScale N)) +
        7 * ((eb + Real.log (1 / chi) / logScale N) / 2) +
        7 * (chi * T + Real.log (1 / chi) / logScale N) +
        (Qerr + A * exceptionalAllowance chi) + 2 * Qerr + 8 * delta + 4 * eb ≤
          3 * eta / 4 := by
    intro er eb delta her heb herBudget hebBudget hdelta
    let A := 4 * Real.log (k : ℝ)
    let Qerr := quadratureError N T rho phi P.cellCount A chi
    have hA : 0 ≤ A := mul_nonneg (by norm_num)
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
    have hL := logScale_pos hN
    have hkinv : 1 / (k : ℝ) ≤ 1 := by
      have hkr : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      exact (div_le_one (by positivity : (0 : ℝ) < k)).mpr hkr
    have hlog : 0 ≤ Real.log (1 / chi) :=
      Real.log_nonneg ((one_le_div hchi).mpr (hchiK.le.trans hkinv))
    have hterm : 0 ≤ (chi + A + 2 * A * P.cellCount) *
        (⌊T / rho⌋₊ + 1 : ℕ) / logScale N := by positivity
    have hAnL : 0 ≤ A / logScale N := div_nonneg hA hL.le
    have hlogL : 0 ≤ Real.log (1 / chi) / logScale N := div_nonneg hlog hL.le
    have hseparate :
        (chi + A + 2 * A * P.cellCount) * (⌊T / rho⌋₊ + 1 : ℕ) / logScale N +
          A / logScale N + Real.log (1 / chi) / logScale N ≤ epsilon / 16 := by
      simpa only [add_div] using hNbudget
    have htermBound :
        (chi + A + 2 * A * P.cellCount) * (⌊T / rho⌋₊ + 1 : ℕ) / logScale N ≤
          epsilon / 16 := by linarith
    have hAnLBound : A / logScale N ≤ epsilon / 16 := by linarith
    have hlogLBound : Real.log (1 / chi) / logScale N ≤ epsilon / 16 := by linarith
    have hQerr0 : 0 ≤ Qerr := quadratureError_nonneg hN hT hrho hphi hA hchi.le
    have hQerrBound : Qerr ≤ 5 * epsilon / 16 := by
      dsimp [Qerr, quadratureError]
      change 2 * chi * T + A * P.cellCount * phi * T + 2 * A * rho +
        (chi + A + 2 * A * P.cellCount) * (⌊T / rho⌋₊ + 1 : ℕ) / logScale N ≤ _
      dsimp [A] at htermBound ⊢
      nlinarith
    have heS : chi * T + Real.log (1 / chi) / logScale N ≤ epsilon / 8 := by linarith
    have heF : (eb + Real.log (1 / chi) / logScale N) / 2 ≤ 17 * epsilon / 32 := by
      linarith
    have hshift : A * (er + 1 / logScale N) = A * er + A / logScale N := by ring
    have heBeta : Qerr + A * (er + 1 / logScale N) ≤ 5 * epsilon / 8 := by
      rw [hshift]
      change A * er ≤ epsilon / 4 at herBudget
      linarith
    have heH : Qerr + A * exceptionalAllowance chi ≤ 9 * epsilon / 16 := by
      change A * exceptionalAllowance chi ≤ epsilon / 4 at hbadBudget
      linarith
    change (7 / 2 : ℝ) * (Qerr + A * (er + 1 / logScale N)) +
      7 * ((eb + Real.log (1 / chi) / logScale N) / 2) +
      7 * (chi * T + Real.log (1 / chi) / logScale N) +
      (Qerr + A * exceptionalAllowance chi) + 2 * Qerr + 8 * delta + 4 * eb ≤ 3 * eta / 4
    have htotal :
        (7 / 2 : ℝ) * (Qerr + A * (er + 1 / logScale N)) +
          7 * ((eb + Real.log (1 / chi) / logScale N) / 2) +
          7 * (chi * T + Real.log (1 / chi) / logScale N) +
          (Qerr + A * exceptionalAllowance chi) + 2 * Qerr + 8 * delta + 4 * eb ≤
            639 * epsilon / 32 := by
      linarith [hdelta.2]
    linarith
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
    have hrepair := hrepairBudget er eb delta her heb herBudget hebBudget hdelta
    obtain ⟨F, hF, hlarge⟩ := source_large_margin cuts hN hk mu P hT hrho hphi
      ⟨hchi, hchiK⟩ (by norm_num) hreg hLike hr0 hrT her heb heta
      (exceptionalAllowance_nonneg chi) hdelta.1 hFM x timeClass hwv hvn hnK hlegal
      hambient hR hcross (by simpa only [one_mul] using hb.1)
    obtain ⟨G, hG, hsmall⟩ := source_small_margin cuts hN hk mu P hT hrho hphi
      ⟨hchi, hchiK⟩ (by norm_num) hreg hLike hr0 hrT her heb heta
      (exceptionalAllowance_nonneg chi) hdelta.1 hFM x timeClass hwv hvn hnK hlegal
      hambient hR hcross (by simpa only [one_mul] using hb.2.1)
    obtain ⟨J, hJ, hcoarse⟩ := source_small_coarse_margin cuts hN hk mu P hT hrho hphi
      ⟨hchi, hchiK⟩ (by norm_num) hreg hLike hr0 hrT her heb heta
      (exceptionalAllowance_nonneg chi) hdelta.1 hFM x timeClass hwv hvn hnK hlegal
      hambient hR hcross (by simpa only [one_mul] using hrepair)
    have hFG : F = G := by exact_mod_cast hF.symm.trans hG
    have hFJ : F = J := by exact_mod_cast hF.symm.trans hJ
    subst G
    subst J
    exact ⟨F, hF, hlarge, hsmall, hcoarse⟩
  · intro er eb delta her heb herBudget hebBudget hdelta x w v hwv hvK hlegal hambient hcross
    have hb := hbudgets er eb 0 her heb herBudget hebBudget ⟨le_rfl, hepsilon.le⟩
    apply source_no_terminal_fallback cuts hN hk mu P hT hrho hphi ⟨hchi, hchiK⟩
      (by norm_num) hreg hLike hr0 hrT her heb heta hdelta hFM x hwv hvK hlegal hambient hcross
    simpa only [one_mul] using hb.2.2.2

end

end InhomogeneousShuffle.FirstMoment.Model
