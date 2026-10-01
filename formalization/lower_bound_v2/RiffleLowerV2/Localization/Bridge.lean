import RiffleLowerV2.Localization.Words

noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2.Localization
open TimeProfile

theorem goodColumn_ordered_digits {k : ℕ} {p : Simplex k} {chi : ℝ}
    (h : GoodColumn p chi) :
    ∃ lo hi : Fin k, lo < hi ∧ chi ≤ prob p lo ∧ chi ≤ prob p hi := by
  rcases h with ⟨lo,hi,hne,hlo,hhi⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨lo,hi,hlt,hlo,hhi⟩
  · exact ⟨hi,lo,hlt,hhi,hlo⟩

private theorem twoMarked_product_lower {k N K : ℕ} (cuts : Cuts k N K)
    (hk : 1 ≤ k) {I : Finset (Fin K)} (v : WordOn k I)
    (jL jR : I) (hne : jL ≠ jR) {chi : ℝ} (hchi : 0 ≤ chi)
    (hL : chi ≤ (cuts.count jL.val (v jL) : ℝ)/N)
    (hR : chi ≤ (cuts.count jR.val (v jR) : ℝ)/N)
    (hother : ∀ j : I, j ≠ jL → j ≠ jR → 1/(k : ℝ) ≤ (cuts.count j.val (v j) : ℝ)/N) :
    chi^2 * (k : ℝ)^(-(I.card : ℝ)) ≤ massOn cuts v := by
  classical
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hinv : 1/(k : ℝ) ≤ 1 := (div_le_one hkpos).mpr hkR
  have hprod : (∏ j : I, (if j=jL then chi else 1) *
      (if j=jR then chi else 1) * (1/(k : ℝ))) ≤ massOn cuts v := by
    apply Finset.prod_le_prod
    · intro j _
      positivity
    · intro j _
      by_cases hl : j=jL
      · subst j
        simp only [ite_true, if_neg hne, mul_one]
        exact (mul_le_of_le_one_right hchi hinv).trans hL
      · by_cases hr : j=jR
        · subst j
          simp only [if_neg hne.symm, ite_true, one_mul]
          exact (mul_le_of_le_one_right hchi hinv).trans hR
        · simpa [hl,hr] using hother j hl hr
  have hcalc : (∏ j : I, (if j=jL then chi else 1) *
      (if j=jR then chi else 1) * (1/(k : ℝ))) =
      chi^2 * (k : ℝ)^(-(I.card : ℝ)) := by
    simp only [Finset.prod_mul_distrib]
    simp [Real.rpow_neg hkpos.le, Real.rpow_natCast, one_div, pow_two]
  rwa [hcalc] at hprod

theorem bridge_log_bound {k N K : ℕ} (cuts : Cuts k N K) (hN2 : 2 ≤ N)
    (hN : 0 < N) (hk : 2 ≤ k) {P : BorelPartition k} {W : ColdWitnessData}
    (G : ColdGeometryData K P W) {rho chi : ℝ} (hrho : 0 < rho) (hchi : 0 < chi)
    (hlen : W.bridgeLength = ⌈2*rho*logScale N⌉₊)
    (hm : chi^2*(k : ℝ)^(-(W.bridgeLength : ℝ)) ≤ massOn cuts G.central) :
    0 ≤ geometryEllB cuts G ∧ geometryEllB cuts G ≤ 2*rho*Real.log k +
      (Real.log k+2*Real.log (1/chi))/logScale N := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0<k)
  have hLpos := logScale_pos hN2
  have hp : 0 < chi^2*(k : ℝ)^(-(W.bridgeLength : ℝ)) := by positivity
  have hmpos : 0 < massOn cuts G.central := hp.trans_le hm
  have hle : massOn cuts G.central ≤ 1 := Types.massOn_le_one cuts hN _
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤k))
  have hc : (W.bridgeLength : ℝ) ≤ 2*rho*logScale N+1 := by
    rw [hlen]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hlog := Real.log_le_log hp hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow hkpos] at hlog
  norm_num at hlog
  have hcost : -Real.log (massOn cuts G.central) ≤
      (2*rho*logScale N+1)*Real.log k+2*Real.log (1/chi) := by
    have hmul := mul_le_mul_of_nonneg_right hc hlogk
    simp only [one_div, Real.log_inv] at *
    nlinarith
  constructor
  · exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hmpos.le hle)) (logScale_pos hN2).le
  · unfold geometryEllB
    apply (div_le_iff₀ (logScale_pos hN2)).mpr
    calc
      -Real.log (massOn cuts G.central) ≤
          (2*rho*logScale N+1)*Real.log k+2*Real.log (1/chi) := hcost
      _ = (2*rho*Real.log k+(Real.log k+2*Real.log (1/chi))/logScale N)*logScale N := by
        field_simp [(logScale_pos hN2).ne']
        ring

/-- The concrete bridge changes only its two designated good coordinates. -/
theorem exists_bridgeGeometry {k N K : ℕ} (cuts : Cuts k N K)
    (hN2 : 2 ≤ N) (hN : 0 < N) (hk : 2 ≤ k)
    {eta rho chi : ℝ} (hrho : 0 < rho) (hchi : 0 < chi)
    (P : BorelPartition k) (W : ColdWitnessData) (a : Word k K)
    (ha : IsCanonicalMaxWord cuts a) (Dp Dt : RoundedTypeData P)
    (hW : WitnessSpec cuts hN eta rho chi W) :
    ∃ G : ColdGeometryData K P W, G.ambient=a ∧ G.prefixType=Dp ∧ G.tailType=Dt ∧
      BridgeSpec cuts hN rho chi G ∧
      ∀ v ∈ ({G.central,G.reserveMinus,G.reservePlus} : Finset (WordOn k (bridgeColumns K W))),
        ∀ j : bridgeColumns K W, min chi (1/(k : ℝ)) ≤ (cuts.count j.val (v j) : ℝ)/N := by
  classical
  obtain ⟨hlen,horder,hK,htheta,hgood,hrest⟩ := hW
  rcases hgood with ⟨gL,gR,hL0,hLR,hR1,hgoodL,hgoodR⟩
  have hgL : gL ∈ bridgeColumns K W := mem_columnSet.mpr ⟨hL0, hLR.trans hR1⟩
  have hgR : gR ∈ bridgeColumns K W := mem_columnSet.mpr ⟨by omega,hR1⟩
  let jL : bridgeColumns K W := ⟨gL,hgL⟩
  let jR : bridgeColumns K W := ⟨gR,hgR⟩
  have hne : jL ≠ jR := by
    intro h
    have hv := congrArg (fun j : bridgeColumns K W => j.val.val) h
    dsimp [jL,jR] at hv
    omega
  obtain ⟨loL,hiL,hltL,hloL,hhiL⟩ := goodColumn_ordered_digits hgoodL
  obtain ⟨loR,hiR,hltR,hloR,hhiR⟩ := goodColumn_ordered_digits hgoodR
  simp only [Cuts.profile_prob] at hloL hhiL hloR hhiR
  let base : WordOn k (bridgeColumns K W) := restrictWord (bridgeColumns K W) a
  let central : WordOn k (bridgeColumns K W) := Function.update (Function.update base jL hiL) jR loR
  let minus : WordOn k (bridgeColumns K W) := Function.update central jL loL
  let plus : WordOn k (bridgeColumns K W) := Function.update central jR hiR
  have hcL : central jL=hiL := by simp [central,hne]
  have hcR : central jR=loR := by simp [central]
  have hminus : wordOnList minus < wordOnList central := by
    apply wordOnList_lt_of_single_change jL
    · simpa [minus,hcL] using hltL
    · intro j hj; simp [minus,hj]
  have hplus : wordOnList central < wordOnList plus := by
    apply wordOnList_lt_of_single_change jR
    · simpa [plus,hcR] using hltR
    · intro j hj; simp [plus,hj]
  have hcommon (v : WordOn k (bridgeColumns K W))
      (hv : v∈({central,minus,plus} : Finset (WordOn k (bridgeColumns K W)))) :
      chi ≤ (cuts.count gL (v jL) : ℝ)/N ∧ chi ≤ (cuts.count gR (v jR) : ℝ)/N ∧
      (∀ j : bridgeColumns K W, j≠jL → j≠jR → v j=a.get j.val) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · refine ⟨?_,?_,?_⟩
      · simpa only [hcL] using hhiL
      · simpa only [hcR] using hloR
      · intro j hjL hjR; simp [central,base,restrictWord,hjL,hjR]
    · refine ⟨?_,?_,?_⟩
      · simpa [minus] using hloL
      · simpa [minus,hne.symm,hcR] using hloR
      · intro j hjL hjR; simp [minus,central,base,restrictWord,hjL,hjR]
    · refine ⟨?_,?_,?_⟩
      · simpa [plus,hne,hcL] using hhiL
      · simpa [plus] using hhiR
      · intro j hjL hjR; simp [plus,central,base,restrictWord,hjL,hjR]
  have hmass (v : WordOn k (bridgeColumns K W))
      (hv : v∈({central,minus,plus} : Finset (WordOn k (bridgeColumns K W)))) :
      chi^2*(k : ℝ)^(-(W.bridgeLength : ℝ)) ≤ massOn cuts v := by
    rcases hcommon v hv with ⟨hvL,hvR,hvo⟩
    have h := twoMarked_product_lower cuts (by omega) v jL jR hne hchi.le hvL hvR (by
      intro j hjL hjR
      rw [hvo j hjL hjR]
      exact canonical_digit_ge_inv cuts hN (by omega) a ha j.val)
    simpa only [bridgeColumns,columnSet_card (Nat.le_add_right W.mu W.bridgeLength) hK,
      Nat.add_sub_cancel_left] using h
  let G : ColdGeometryData K P W := ⟨a,Dp,Dt,central,minus,plus,gL,gR⟩
  have hlog := bridge_log_bound cuts hN2 hN hk G hrho hchi hlen
    (hmass central (by simp))
  refine ⟨G,rfl,rfl,rfl,?_,?_⟩
  · refine ⟨hgL,hgR,hLR,hgoodL,hgoodR,hminus,hplus,?_,?_,?_,hlog.1,hlog.2⟩
    · intro j hj
      have hj' : j≠jL := by intro h; apply hj; exact congrArg Subtype.val h
      change minus j=central j
      simp [minus,hj']
    · intro j hj
      have hj' : j≠jR := by intro h; apply hj; exact congrArg Subtype.val h
      change plus j=central j
      simp [plus,hj']
    · exact hmass
  · intro v hv j
    rcases hcommon v hv with ⟨hvL,hvR,hvo⟩
    by_cases hjL : j=jL
    · subst j; exact (min_le_left _ _).trans hvL
    · by_cases hjR : j=jR
      · subst j; exact (min_le_left _ _).trans hvR
      · rw [hvo j hjL hjR]
        exact (min_le_right _ _).trans (canonical_digit_ge_inv cuts hN (by omega) a ha j.val)

end RiffleLowerV2.Localization
