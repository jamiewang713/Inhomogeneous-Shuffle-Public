import RiffleLowerV2.Localization.ProbabilityIntervals

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Localization
open TimeProfile
attribute [local instance] Classical.propDecidable

/-- Explicit lattice and boundary estimates for the actual selected cold intervals. -/
theorem coldRelativeSet_estimates {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (hN2 : 2 ≤ N) (P : BorelPartition k) (W : ColdWitnessData)
    (G : ColdGeometryData K P W) {xi kap : ℝ} (hkap : 0 < kap)
    (hlog : 12/kap ≤ logScale N)
    (hmean : prefixMean cuts (prefixAt W.ms G.ambient) = (N : ℝ)^(beta cuts hN (W.s N)))
    (hspec : TypeDataSpec cuts hN P (prefixColumns K W) xi W.theta G.prefixType)
    (hell : beta cuts hN (W.s N)/2+2*kap ≤ geometryEllP cuts hN P W G)
    (hhp : typeH cuts hN P (prefixColumns K W) G.prefixType ≤ geometryEllP cuts hN P W G-kap)
    (hh : kap/2 ≤ geometryH cuts hN P W G) :
    Real.exp (-2)*(N : ℝ)^(geometryH cuts hN P W G) ≤
      ((coldRelativeSet cuts hN P W G).card : ℝ) ∧
    ((coldRelativeSet cuts hN P W G).card : ℝ) ≤ 2*(N : ℝ)^(geometryH cuts hN P W G) ∧
    (N : ℝ)^(kap/3) ≤ ((coldRelativeSet cuts hN P W G).card : ℝ) ∧
    ((coldRelativeSet cuts hN P W G).card : ℝ) ≤ N ∧
    (∀ q : Fin (N+1), ((boundary (clipTranslate N (coldRelativeSet cuts hN P W G) q.val)).card : ℝ) ≤
      4*Real.sqrt ((coldRelativeSet cuts hN P W G).card : ℝ)) := by
  rcases hspec with ⟨_, _, _, _, _, _, _, _, _, _, hJ, _, hcard, hmass, _⟩
  let b := beta cuts hN (W.s N)
  let ell := geometryEllP cuts hN P W G
  let hp := typeH cuts hN P (prefixColumns K W) G.prefixType
  let H := coldRelativeSet cuts hN P W G
  let F := coldPrefixFamily cuts hN P W G
  let Q := (N : ℝ)^ell
  let C := (F.card : ℝ)
  let M := (H.card : ℝ)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < logScale N := logScale_pos hN2
  have hlogmul : 12 ≤ kap*logScale N := by
    have := (div_le_iff₀ hkap).mp hlog
    nlinarith
  have hb : 4*kap ≤ b := by dsimp [geometryEllP] at hell; dsimp [b]; linarith
  have hell4 : 4*kap ≤ ell := by dsimp [ell, b] at *; linarith
  have hQpos : 0 < Q := Real.rpow_pos_of_pos hNp _
  have hC : C = (N : ℝ)^hp := hcard
  have hCQ : C*Q = (N : ℝ)^(geometryH cuts hN P W G) := by
    rw [hC]
    dsimp [Q, geometryH, ell, hp]
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hQ : Real.exp 2 ≤ Q := by
    dsimp [Q]
    rw [Real.rpow_def_of_pos hNp]
    apply Real.exp_le_exp.mpr
    change 2 ≤ logScale N*ell
    nlinarith [mul_le_mul_of_nonneg_left hell4 hL.le]
  have hmu : 0 ≤ prefixMean cuts (prefixAt W.ms G.ambient) := by rw [hmean]; positivity
  have hmassQ : ∀ x ∈ F, Real.exp (-1)*Q ≤
      prefixMean cuts (prefixAt W.ms G.ambient)*massOn cuts x ∧
      prefixMean cuts (prefixAt W.ms G.ambient)*massOn cuts x ≤ Q := by
    intro x hx
    have hm := hmass x hx
    have hl := mul_le_mul_of_nonneg_left hm.1.le (Real.rpow_pos_of_pos hNp b).le
    have hu := mul_le_mul_of_nonneg_left hm.2 (Real.rpow_pos_of_pos hNp b).le
    have hid : (N : ℝ)^b*(N : ℝ)^(-typeJ N G.prefixType) = Q := by
      rw [← Real.rpow_add hNp]
      rfl
    rw [hmean]
    change Real.exp (-1)*Q ≤ (N : ℝ)^b*massOn cuts x ∧ (N : ℝ)^b*massOn cuts x ≤ Q
    constructor
    · calc
        Real.exp (-1)*Q = (N : ℝ)^b*(Real.exp (-1)*(N : ℝ)^(-typeJ N G.prefixType)) := by rw [← hid]; ring
        _ ≤ _ := hl
    · exact hu.trans_eq hid
  have hcounts : C*(Real.exp (-1)*Q-1) ≤ M ∧ M ≤ C*(Q+1) :=
    probabilityIntervals_card_bounds cuts F hmu hmassQ
  have he2 : 0 < Real.exp (-2 : ℝ) := Real.exp_pos _
  have heg : 2*Real.exp (-2 : ℝ) ≤ Real.exp (-1 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (1 : ℝ)) he2.le
    have he : Real.exp (1 : ℝ)*Real.exp (-2) = Real.exp (-1) := by
      rw [← Real.exp_add]
      norm_num
    rw [he] at h
    norm_num at h ⊢
    exact h
  have hunit : 1 ≤ Real.exp (-2 : ℝ)*Q := by
    have h := mul_le_mul_of_nonneg_left hQ he2.le
    simpa only [← Real.exp_add, show (-2 : ℝ)+2 = 0 by norm_num, Real.exp_zero] using h
  have hQ1 : 1 ≤ Q := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hQ
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have hlo : Real.exp (-2)*(N : ℝ)^(geometryH cuts hN P W G) ≤ M := by
    rw [← hCQ]
    have hg := mul_le_mul_of_nonneg_right heg hQpos.le
    have hb : Real.exp (-2)*Q ≤ Real.exp (-1)*Q-1 := by nlinarith
    have hc := mul_le_mul_of_nonneg_left hb hC0
    nlinarith [hcounts.1]
  have hup : M ≤ 2*(N : ℝ)^(geometryH cuts hN P W G) := by
    rw [← hCQ]
    nlinarith [hcounts.2, mul_nonneg hC0 (sub_nonneg.mpr hQ1)]
  have hsmall : (N : ℝ)^(kap/3) ≤ Real.exp (-2)*(N : ℝ)^(geometryH cuts hN P W G) := by
    rw [Real.rpow_def_of_pos hNp, Real.rpow_def_of_pos hNp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change logScale N*(kap/3) ≤ -2+logScale N*geometryH cuts hN P W G
    nlinarith [mul_le_mul_of_nonneg_left hh hL.le]
  have hpop : M ≤ N := by
    dsimp [M, H, coldRelativeSet]
    exact_mod_cast probabilityIntervals_card_le_population cuts hN F hmu
      (prefixMean_le_population cuts hN _)
  have hCsq : C^2 ≤ Real.exp (-2)*(N : ℝ)^(geometryH cuts hN P W G) := by
    rw [hC, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    rw [Real.rpow_def_of_pos hNp, Real.rpow_def_of_pos hNp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change logScale N*(hp*2) ≤ -2+logScale N*(ell+hp)
    have hhp' : hp ≤ ell-kap := hhp
    nlinarith [mul_le_mul_of_nonneg_left hhp' hL.le]
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hCsqrt : C ≤ Real.sqrt M := (Real.le_sqrt hC0 hM0).mpr (hCsq.trans hlo)
  have hM1 : 1 ≤ M := (Real.one_le_rpow hN1 (by positivity : (0 : ℝ) ≤ kap/3)).trans (hsmall.trans hlo)
  have hsqrt1 : 1 ≤ Real.sqrt M := by simpa using Real.sqrt_le_sqrt hM1
  refine ⟨hlo, hup, hsmall.trans hlo, hpop, ?_⟩
  intro q
  have hbound : (integerBoundary H).card ≤ 2*F.card :=
    integerBoundary_intervalUnion_card_le F
      (fun x => prefixMean cuts (prefixAt W.ms G.ambient)*relativeMassBefore cuts x)
      (fun x => prefixMean cuts (prefixAt W.ms G.ambient)*(relativeMassBefore cuts x+massOn cuts x))
  have hbnd := (boundary_clipTranslate_le N H q.val).trans (Nat.add_le_add_right hbound 2)
  have hbndR : ((boundary (clipTranslate N H q.val)).card : ℝ) ≤ 2*C+2 := by
    dsimp [C]
    exact_mod_cast hbnd
  change ((boundary (clipTranslate N H q.val)).card : ℝ) ≤ 4*Real.sqrt M
  linarith

end RiffleLowerV2.Localization
