import RiffleLowerV2.EmpiricalLower.CollisionMean

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Topology
open Filter
namespace RiffleLowerV2.EmpiricalLower
open TimeProfile Factorial

/-- No independence is needed to intersect the count and localization events. -/
theorem probability_intersection_lower {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (A B : Ω → Prop) :
    probability P A + probability P B - 1 ≤ probability P (fun ω => A ω ∧ B ω) := by
  have hpoint (ω : Ω) : (if A ω then (1 : ℝ) else 0) +
      (if B ω then (1 : ℝ) else 0) - 1 ≤ (if A ω ∧ B ω then (1 : ℝ) else 0) := by
    by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha, hb]
  have h := expect_mono P hpoint
  simp only [expect_sub, expect_add, expect_const] at h
  refine h.trans (le_of_eq ?_)
  unfold probability
  congr 1
  funext ω
  by_cases hab : A ω ∧ B ω <;> simp [hab]

theorem collisionCount_eq_card {k N K : ℕ} {cuts : Cuts k N K}
    (Y : Finset (Word k K)) (ω : Sample cuts) :
    collisionCount Y ω = ((Y.filter (fun y => 2 ≤ wordCount y ω)).card : ℝ) := by
  simp only [collisionCount, collisionEvent, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hc : 2 ≤ wordCount y ω <;> simp [hc]

theorem cold_mean_power_lower {N : ℕ} (hN : 0 < N) {eta M E : ℝ}
    (hMlower : (N : ℝ)^(kappa eta/3) ≤ M)
    (hmean : Real.sqrt M*(N : ℝ)^(kappa eta/3) ≤ E) :
    (N : ℝ)^(kappa eta/2) ≤ E := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := Real.sqrt_le_sqrt hMlower
  have hid : Real.sqrt ((N : ℝ)^(kappa eta/3)) = (N : ℝ)^(kappa eta/6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]
    congr 1
    ring
  rw [hid] at hs
  have hh := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hNp.le (kappa eta/3))
  rw [← Real.rpow_add hNp] at hh
  have he : kappa eta/6+kappa eta/3 = kappa eta/2 := by ring
  rw [he] at hh
  exact hh.trans hmean

theorem cold_half_mean_threshold {N : ℕ} (hN : 0 < N) {eta M E : ℝ}
    (hlarge : 2 ≤ (N : ℝ)^(kappa eta/12))
    (hmean : Real.sqrt M*(N : ℝ)^(kappa eta/3) ≤ E) :
    Real.sqrt M*(N : ℝ)^(kappa eta/4) ≤ E/2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := mul_le_mul_of_nonneg_left hlarge
    (show 0 ≤ Real.sqrt M*(N : ℝ)^(kappa eta/4) by positivity)
  have hid : (N : ℝ)^(kappa eta/4)*(N : ℝ)^(kappa eta/12) =
      (N : ℝ)^(kappa eta/3) := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  simp only [mul_assoc] at hh
  rw [hid] at hh
  linarith

theorem cold_edges_threshold {N : ℕ} (hN : 1 ≤ N) {eta M : ℝ} (heta : 0 < eta)
    (hM : 0 < M) (hMN : M ≤ N) :
    M^(1/2+kappa eta/5) ≤ Real.sqrt M*(N : ℝ)^(kappa eta/4) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hκ : 0 < kappa eta := by unfold kappa; positivity
  rw [Real.rpow_add hM, Real.sqrt_eq_rpow]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hM.le _)
  exact (Real.rpow_le_rpow hM.le hMN (by positivity : 0 ≤ kappa eta/5)).trans
    (Real.rpow_le_rpow_of_exponent_le hNr (by linarith : kappa eta/5 ≤ kappa eta/4))

/-- Many edges from the actual finite collision law and the proved localization event.
All thresholds precede the cuts and every witness and geometry choice. -/
theorem manyEdges : Targets.ManyEdgesTarget := by
  intro k hk T eta rho chi xi hT heta hrho hchi hxi P epsilon hepsilon
  have hκ : 0 < kappa eta := by unfold kappa; positivity
  let c : ℝ := min xi (min chi (1/(k : ℝ)))
  have hc : 0 < c := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    dsimp [c]
    positivity
  obtain ⟨D, hD, No, ho⟩ := Occupancy.uniformOccupancy c T hc hT
  obtain ⟨Nm, hNm, hm⟩ := exists_cold_mean_threshold eta heta
  obtain ⟨Nl, _, hl⟩ := Localization.localization k hk T eta rho chi xi hT heta hrho hchi hxi
    P (epsilon/2) (by positivity)
  obtain ⟨Ns, hs⟩ := eventually_atTop.mp (Occupancy.eventually_negative_rpow_le
    (by norm_num : (-1/100 : ℝ) < 0)
    (show 0 < min (1/(2*D)) (epsilon/(16*D)) by positivity))
  obtain ⟨Ne, he⟩ := eventually_atTop.mp (Occupancy.eventually_negative_rpow_le
    (show -(kappa eta/2) < 0 by linarith) (show 0 < epsilon/16 by positivity))
  let N0 := max (max No Nm) (max Nl (max Ns Ne))
  have hNm0 : Nm ≤ N0 := (le_max_right No Nm).trans (le_max_left _ _)
  refine ⟨N0, hNm.trans hNm0, ?_⟩
  intro N hlarge cuts hN W G hW hG
  have hNoN : No ≤ N := ((le_max_left No Nm).trans (le_max_left _ _)).trans hlarge
  have hNmN : Nm ≤ N := hNm0.trans hlarge
  have hNlN : Nl ≤ N := ((le_max_left Nl (max Ns Ne)).trans (le_max_right _ _)).trans hlarge
  have hNsN : Ns ≤ N := ((le_max_left Ns Ne).trans
    ((le_max_right Nl (max Ns Ne)).trans (le_max_right _ _))).trans hlarge
  have hNeN : Ne ≤ N := ((le_max_right Ns Ne).trans
    ((le_max_right Nl (max Ns Ne)).trans (le_max_right _ _))).trans hlarge
  have hN2 : 2 ≤ N := hNm.trans hNmN
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : (horizonDepth N T : ℝ) ≤ T*logScale N :=
    Nat.floor_le (mul_nonneg hT.le (logScale_pos hN2).le)
  let Y := coldFullFamily cuts hN P W G
  let Hrel := coldRelativeSet cuts hN P W G
  let M : ℝ := Hrel.card
  let E := expect (fixedCountPMF cuts) (collisionCount Y)
  have hselected : selectedPiles cuts Y c := geometry_selectedPiles cuts hN P W G hG
  obtain ⟨hmarg, _, hvar⟩ := ho N hNoN k (horizonDepth N T) hK cuts Y hselected
  have hsmall : D*(N : ℝ)^(-1/100 : ℝ) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left ((hs N hNsN).trans (min_le_left _ _)) hD.le
    have hid : D*(1/(2*D)) = 1/2 := by field_simp
    rwa [hid] at hh
  have hsmallE : 4*D*(N : ℝ)^(-1/100 : ℝ) ≤ epsilon/4 := by
    have hh := mul_le_mul_of_nonneg_left ((hs N hNsN).trans (min_le_right _ _))
      (show 0 ≤ 4*D by positivity)
    have hid : 4*D*(epsilon/(16*D)) = epsilon/4 := by field_simp; ring
    rwa [hid] at hh
  have hmean := cold_collision_mean_lower cuts hN heta P W G hG hsmall hmarg
  have hGfull := hG
  rcases hG with ⟨_, _, _, _, _, _, _, _, _, _, _, hMupper, hMlower, hMN, _, hgap, _⟩
  have hMpos : 0 < M := (Real.rpow_pos_of_pos hNp (kappa eta/3)).trans_le hMlower
  have hmean' : Real.sqrt M*(N : ℝ)^(kappa eta/3) ≤ E :=
    cold_mean_dominates hN1 heta hMpos.le hMupper hgap (hm N hNmN).1 hmean
  have hpower : (N : ℝ)^(kappa eta/2) ≤ E := cold_mean_power_lower hN hMlower hmean'
  have hEpos : 0 < E := (Real.rpow_pos_of_pos hNp _).trans_le hpower
  have hhalflarge := cold_half_mean_threshold hN (hm N hNmN).2 hmean'
  have hthreshold := cold_edges_threshold hN1 heta hMpos hMN
  have hrecip : 4/E ≤ epsilon/4 := by
    have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4)
      (Real.rpow_pos_of_pos hNp (kappa eta/2)) hpower
    have hid : 4/(N : ℝ)^(kappa eta/2) = 4*(N : ℝ)^(-(kappa eta/2)) := by
      rw [Real.rpow_neg hNp.le]
      rfl
    rw [hid] at hdiv
    have hh := mul_le_mul_of_nonneg_left (he N hNeN) (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have hcollision : 1-epsilon/2 ≤ probability (fixedCountPMF cuts)
      (fun ω => E/2 ≤ collisionCount Y ω) := by
    have hh := Occupancy.lower_tail_success (fixedCountPMF cuts) (collisionCount Y)
      (D*(N : ℝ)^(-1/100 : ℝ)) (1/2) hEpos (by norm_num) hvar
    have hh' : 1-4/E-4*D*(N : ℝ)^(-1/100 : ℝ) ≤ probability (fixedCountPMF cuts)
        (fun ω => E/2 < collisionCount Y ω) := by
      convert hh using 1 <;> dsimp [E] <;> ring_nf
    have hm' := Occupancy.probability_mono (fixedCountPMF cuts)
      (fun ω (hw : E/2 < collisionCount Y ω) => hw.le)
    linarith
  have hloc' : 1-epsilon/2 ≤ probability (fixedCountPMF cuts) (ColdLocalization hN P W G) := by
    exact hl N hNlN cuts hN W G hW hGfull
  have hinter := probability_intersection_lower (fixedCountPMF cuts)
    (fun ω => E/2 ≤ collisionCount Y ω) (ColdLocalization hN P W G)
  have hmono : probability (fixedCountPMF cuts)
      (fun ω => E/2 ≤ collisionCount Y ω ∧ ColdLocalization hN P W G ω) ≤
      probability (fixedCountPMF cuts) (fun ω =>
        M^(1/2+kappa eta/5) ≤ ((shuffleEdges ω ∩ internalEdges (clipTranslate N Hrel
          (lowerRank (prefixAt W.ms G.ambient) ω : ℤ))).card : ℝ)) := by
    apply Occupancy.probability_mono
    intro ω hω
    have hedge := hω.2.2
    have hc : collisionCount Y ω ≤ ((shuffleEdges ω ∩ internalEdges (clipTranslate N Hrel
          (lowerRank (prefixAt W.ms G.ambient) ω : ℤ))).card : ℝ) := by
      rw [collisionCount_eq_card]
      exact_mod_cast hedge
    exact hthreshold.trans (hhalflarge.trans (hω.1.trans hc))
  dsimp only
  change 1-epsilon ≤ probability (fixedCountPMF cuts) (fun ω =>
    M^(1/2+kappa eta/5) ≤ ((shuffleEdges ω ∩ internalEdges (clipTranslate N Hrel
      (lowerRank (prefixAt W.ms G.ambient) ω : ℤ))).card : ℝ))
  linarith

end RiffleLowerV2.EmpiricalLower
