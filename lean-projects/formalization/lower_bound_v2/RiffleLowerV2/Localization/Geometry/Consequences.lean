import RiffleLowerV2.Localization.Bridge

noncomputable section
open scoped BigOperators
open TimeProfile
namespace RiffleLowerV2.Localization
attribute [local instance] Classical.propDecidable

theorem selected_digit_lower {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) {xi alpha : ℝ} (D : RoundedTypeData P)
    (hD : TypeDataSpec cuts hN P I xi alpha D) (x : WordOn k I)
    (hx : x ∈ selectedClass cuts hN P I D) (j : I) :
    xi ≤ (cuts.count j.val (x j) : ℝ)/N := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hdigit⟩
  exact hdigit x (Finset.mem_filter.mp hx).1 j

theorem massOn_eq_rpow_geometryEllB {k N K : ℕ} (hN2 : 2 ≤ N)
    (cuts : Cuts k N K) {P : BorelPartition k} {W : ColdWitnessData}
    (G : ColdGeometryData K P W) (hpos : 0 < massOn cuts G.central) :
    massOn cuts G.central = (N : ℝ)^(-geometryEllB cuts G) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.rpow_def_of_pos hNr]
  have he : Real.log (N : ℝ)*(-geometryEllB cuts G) = Real.log (massOn cuts G.central) := by
    have hlog : Real.log (N : ℝ) ≠ 0 := (logScale_pos hN2).ne'
    unfold geometryEllB logScale
    field_simp [hlog]
  rw [he, Real.exp_log hpos]

theorem coldFullFamily_card_rpow {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) {xi : ℝ}
    (hp : TypeDataSpec cuts hN P (prefixColumns K W) xi W.theta G.prefixType)
    (ht : TypeDataSpec cuts hN P (tailColumns K W) xi 2 G.tailType) :
    ((coldFullFamily cuts hN P W G).card : ℝ) =
      (N : ℝ)^(typeH cuts hN P (prefixColumns K W) G.prefixType +
        typeH cuts hN P (tailColumns K W) G.tailType) := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hpc, _, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, htc, _, _⟩
  rw [coldFullFamily_card, Nat.cast_mul]
  change (selectedClass cuts hN P (prefixColumns K W) G.prefixType).card *
    ((selectedClass cuts hN P (tailColumns K W) G.tailType).card : ℝ) = _
  rw [hpc, htc, Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N)]

theorem coldFullFamily_mass_bounds {k N K : ℕ} (cuts : Cuts k N K) (hN2 : 2 ≤ N)
    (hN : 0 < N) (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W)
    {xi : ℝ} (hW : W.ms ≤ W.mu) (hK : W.mu+W.bridgeLength ≤ K)
    (ha : prefixMean cuts (prefixAt W.ms G.ambient) = (N : ℝ)^(beta cuts hN (W.s N)))
    (hp : TypeDataSpec cuts hN P (prefixColumns K W) xi W.theta G.prefixType)
    (ht : TypeDataSpec cuts hN P (tailColumns K W) xi 2 G.tailType)
    (hcentral : 0 < massOn cuts G.central) :
    ∀ y ∈ coldFullFamily cuts hN P W G,
      Real.exp (-2)*(N : ℝ)^(geometryZ cuts hN P W G) < (N : ℝ)*wordMass cuts y ∧
      (N : ℝ)*wordMass cuts y ≤ (N : ℝ)^(geometryZ cuts hN P W G) := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpm, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, htm, _⟩
  intro y hy
  obtain ⟨⟨x,z⟩, hxz, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hx,hz⟩ := Finset.mem_product.mp hxz
  have hpx := hpm x hx
  have htz := htm z hz
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : 0 < massOn cuts x := (by positivity : 0 < Real.exp (-1)*(N : ℝ)^(-typeJ N G.prefixType)).trans hpx.1
  have ht0 : 0 < massOn cuts z := (by positivity : 0 < Real.exp (-1)*(N : ℝ)^(-typeJ N G.tailType)).trans htz.1
  have hprodlo : (Real.exp (-1)*(N : ℝ)^(-typeJ N G.prefixType))*
      (Real.exp (-1)*(N : ℝ)^(-typeJ N G.tailType)) < massOn cuts x*massOn cuts z := by
    calc
      _ < (Real.exp (-1)*(N : ℝ)^(-typeJ N G.prefixType))*massOn cuts z :=
        mul_lt_mul_of_pos_left htz.1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hpx.1.le ht0.le
  have hprodup : massOn cuts x*massOn cuts z ≤
      (N : ℝ)^(-typeJ N G.prefixType)*(N : ℝ)^(-typeJ N G.tailType) :=
    mul_le_mul hpx.2 htz.2 ht0.le (by positivity)
  have hm : (N : ℝ)*wordMass cuts (joinColdWord G x G.central z) =
      (N : ℝ)^(beta cuts hN (W.s N))*massOn cuts G.central*(massOn cuts x*massOn cuts z) := by
    rw [joinColdWord_mass cuts G hW hK]
    have hmean : (N : ℝ)*prefixMass cuts (prefixAt W.ms G.ambient) =
      (N : ℝ)^(beta cuts hN (W.s N)) := ha
    calc
      _ = ((N : ℝ)*prefixMass cuts (prefixAt W.ms G.ambient))*massOn cuts G.central*(massOn cuts x*massOn cuts z) := by ring
      _ = _ := by rw [hmean]
  have hid : (N : ℝ)^(beta cuts hN (W.s N))*massOn cuts G.central*
      ((N : ℝ)^(-typeJ N G.prefixType)*(N : ℝ)^(-typeJ N G.tailType)) =
      (N : ℝ)^(geometryZ cuts hN P W G) := by
    rw [massOn_eq_rpow_geometryEllB hN2 cuts G hcentral,
      ← Real.rpow_add hNr, ← Real.rpow_add hNr, ← Real.rpow_add hNr]
    congr 1
    unfold geometryZ
    ring
  have hscale : 0 < (N : ℝ)^(beta cuts hN (W.s N))*massOn cuts G.central := by positivity
  have hlo := mul_lt_mul_of_pos_left hprodlo hscale
  have hup := mul_le_mul_of_nonneg_left hprodup hscale.le
  have hel : Real.exp (-1 : ℝ)*Real.exp (-1) = Real.exp (-2) := by
    rw [← Real.exp_add]
    norm_num
  rw [hm]
  constructor
  · calc
      Real.exp (-2)*(N : ℝ)^geometryZ cuts hN P W G =
          ((N : ℝ)^(beta cuts hN (W.s N))*massOn cuts G.central)*
          ((Real.exp (-1)*(N : ℝ)^(-typeJ N G.prefixType))*(Real.exp (-1)*(N : ℝ)^(-typeJ N G.tailType))) := by
        rw [← hid, ← hel]
        ring
      _ < _ := hlo
  · exact hup.trans_eq hid

theorem joinColdWord_digit_lower {k N K : ℕ} (cuts : Cuts k N K)
    {P : BorelPartition k} {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W))
    (z : WordOn k (tailColumns K W)) (c : ℝ)
    (ha : ∀ j, c ≤ (cuts.count j (G.ambient.get j) : ℝ)/N)
    (hx : ∀ j, c ≤ (cuts.count j.val (x j) : ℝ)/N)
    (hv : ∀ j, c ≤ (cuts.count j.val (v j) : ℝ)/N)
    (hz : ∀ j, c ≤ (cuts.count j.val (z j) : ℝ)/N) (j : Fin K) :
    c ≤ (cuts.count j ((joinColdWord G x v z).get j) : ℝ)/N := by
  by_cases hjp : j ∈ prefixColumns K W
  · simpa only [joinColdWord_get_prefix G x v z ⟨j,hjp⟩] using hx ⟨j,hjp⟩
  · by_cases hjb : j ∈ bridgeColumns K W
    · simpa only [joinColdWord_get_bridge G x v z ⟨j,hjb⟩] using hv ⟨j,hjb⟩
    · by_cases hjt : j ∈ tailColumns K W
      · simpa only [joinColdWord_get_tail G x v z ⟨j,hjt⟩] using hz ⟨j,hjt⟩
      · simpa only [joinColdWord, List.Vector.get_ofFn, dif_neg hjp, dif_neg hjb, dif_neg hjt] using ha j

theorem reservePrefix_mean_lower {k N K : ℕ} (cuts : Cuts k N K)
    (hk : 2 ≤ k) (hN2 : 2 ≤ N) (hN : 0 < N) (P : BorelPartition k)
    (W : ColdWitnessData) (G : ColdGeometryData K P W) {rho chi xi : ℝ}
    (hrho : 0 < rho) (hchi : 0 < chi) (hW : W.ms ≤ W.mu)
    (hK : W.mu+W.bridgeLength ≤ K) (hbl : W.bridgeLength = ⌈2*rho*logScale N⌉₊)
    (ha : prefixMean cuts (prefixAt W.ms G.ambient) = (N : ℝ)^(beta cuts hN (W.s N)))
    (hp : TypeDataSpec cuts hN P (prefixColumns K W) xi W.theta G.prefixType)
    (hbr : BridgeSpec cuts hN rho chi G)
    (x : WordOn k (prefixColumns K W)) (hx : x ∈ coldPrefixFamily cuts hN P W G)
    (v : WordOn k (bridgeColumns K W)) (hv : v ∈ ({G.central,G.reserveMinus,G.reservePlus} : Finset _)) :
    Real.exp (-1)*chi^2*(k : ℝ)^(-1 : ℝ)*
      (N : ℝ)^(geometryEllP cuts hN P W G-2*rho*Real.log k) ≤ prefixMean cuts (reservePrefix G x v) := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpm, _⟩
  rcases hbr with ⟨_, _, _, _, _, _, _, _, _, hmass, _, _⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hL := logScale_pos hN2
  have hlen : (W.bridgeLength : ℝ) ≤ 2*rho*logScale N+1 := by
    rw [hbl]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hkpow : (k : ℝ)^(-1 : ℝ)*(N : ℝ)^(-2*rho*Real.log k) ≤
      (k : ℝ)^(-(W.bridgeLength : ℝ)) := by
    calc
      _ = (k : ℝ)^(-(2*rho*logScale N+1)) := by
        rw [Real.rpow_def_of_pos hkr, Real.rpow_def_of_pos hNr,
          Real.rpow_def_of_pos hkr, ← Real.exp_add]
        congr 1
        dsimp [logScale]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk1 (neg_le_neg hlen)
  have hvlow : chi^2*(k : ℝ)^(-1 : ℝ)*(N : ℝ)^(-2*rho*Real.log k) ≤ massOn cuts v := by
    have h := mul_le_mul_of_nonneg_left hkpow (sq_nonneg chi)
    have h' : chi^2*(k : ℝ)^(-1 : ℝ)*(N : ℝ)^(-2*rho*Real.log k) ≤
        chi^2*(k : ℝ)^(-(W.bridgeLength : ℝ)) := by simpa only [mul_assoc] using h
    exact h'.trans (hmass v hv)
  have hpx := (hpm x hx).1.le
  have hpx' : Real.exp (-1)*(N : ℝ)^(geometryEllP cuts hN P W G) ≤
      (N : ℝ)^(beta cuts hN (W.s N))*massOn cuts x := by
    have h := mul_le_mul_of_nonneg_left hpx (Real.rpow_pos_of_pos hNr (beta cuts hN (W.s N))).le
    have he : (N : ℝ)^(beta cuts hN (W.s N))*(N : ℝ)^(-typeJ N G.prefixType) =
        (N : ℝ)^(geometryEllP cuts hN P W G) := by rw [← Real.rpow_add hNr]; rfl
    calc
      _ = (N : ℝ)^(beta cuts hN (W.s N))*(Real.exp (-1)*(N : ℝ)^(-typeJ N G.prefixType)) := by rw [← he]; ring
      _ ≤ _ := h
  have hp0 : 0 ≤ (N : ℝ)^(beta cuts hN (W.s N))*massOn cuts x :=
    (by positivity : 0 ≤ Real.exp (-1)*(N : ℝ)^(geometryEllP cuts hN P W G)).trans hpx'
  have hprod := mul_le_mul hpx' hvlow (by positivity) hp0
  rw [reservePrefix_mean cuts G hW hK, ha]
  calc
    _ = (Real.exp (-1)*(N : ℝ)^(geometryEllP cuts hN P W G))*
        (chi^2*(k : ℝ)^(-1 : ℝ)*(N : ℝ)^(-2*rho*Real.log k)) := by
      have he : (N : ℝ)^(geometryEllP cuts hN P W G)*(N : ℝ)^(-2*rho*Real.log k) =
          (N : ℝ)^(geometryEllP cuts hN P W G-2*rho*Real.log k) := by
        rw [← Real.rpow_add hNr]
        congr 1
        ring
      rw [← he]
      ring
    _ ≤ _ := hprod

theorem cold_selected_digits {k N K : ℕ} (cuts : Cuts k N K) (hk : 2 ≤ k) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) {xi chi : ℝ}
    (hxi : 0 < xi) (hchi : 0 < chi) (ha : IsCanonicalMaxWord cuts G.ambient)
    (hp : TypeDataSpec cuts hN P (prefixColumns K W) xi W.theta G.prefixType)
    (ht : TypeDataSpec cuts hN P (tailColumns K W) xi 2 G.tailType)
    (hb : ∀ v ∈ ({G.central,G.reserveMinus,G.reservePlus} : Finset (WordOn k (bridgeColumns K W))),
      ∀ j : bridgeColumns K W, min chi (1/(k : ℝ)) ≤ (cuts.count j.val (v j) : ℝ)/N) :
    let c := min xi (min chi (1/(k : ℝ)))
    0 < c ∧
    (∀ y ∈ coldFullFamily cuts hN P W G, ∀ j : Fin K, c ≤ (cuts.count j (y.get j) : ℝ)/N) ∧
    (∀ x ∈ coldPrefixFamily cuts hN P W G,
      ∀ v ∈ ({G.reserveMinus,G.reservePlus} : Finset (WordOn k (bridgeColumns K W))),
      ∀ j : Fin (reservePrefix G x v).1.val,
        c ≤ (cuts.count ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ (reservePrefix G x v).1.isLt)⟩
          ((reservePrefix G x v).2.get j) : ℝ)/N) := by
  dsimp only
  let c := min xi (min chi (1/(k : ℝ)))
  have hk0 : 0 < k := by omega
  have hcxi : c ≤ xi := min_le_left _ _
  have hcbr : c ≤ min chi (1/(k : ℝ)) := min_le_right _ _
  have hca : ∀ j : Fin K, c ≤ (cuts.count j (G.ambient.get j) : ℝ)/N := by
    intro j
    exact (hcbr.trans (min_le_right _ _)).trans (canonical_digit_ge_inv cuts hN hk0 G.ambient ha j)
  have hcx : ∀ x ∈ coldPrefixFamily cuts hN P W G, ∀ j,
      c ≤ (cuts.count j.val (x j) : ℝ)/N := by
    intro x hx j
    exact hcxi.trans (selected_digit_lower cuts hN P _ G.prefixType hp x hx j)
  have hcz : ∀ z ∈ coldTailFamily cuts hN P W G, ∀ j,
      c ≤ (cuts.count j.val (z j) : ℝ)/N := by
    intro z hz j
    exact hcxi.trans (selected_digit_lower cuts hN P _ G.tailType ht z hz j)
  refine ⟨by positivity, ?_, ?_⟩
  · intro y hy j
    obtain ⟨⟨x,z⟩, hxz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hx,hz⟩ := Finset.mem_product.mp hxz
    exact joinColdWord_digit_lower cuts G x G.central z c hca (hcx x hx)
      (fun j => hcbr.trans (hb G.central (by simp) j)) (hcz z hz) j
  · intro x hx v hv j
    have hv' : v ∈ ({G.central,G.reserveMinus,G.reservePlus} : Finset (WordOn k (bridgeColumns K W))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      exact Or.inr hv
    have hjoin := joinColdWord_digit_lower cuts G x v (restrictWord (tailColumns K W) G.ambient) c hca
      (hcx x hx) (fun j => hcbr.trans (hb v hv' j)) (fun j => hca j.val)
    change Fin (min (W.mu+W.bridgeLength) K) at j
    change c ≤ (cuts.count _ ((List.Vector.ofFn _).get j) : ℝ)/N
    rw [List.Vector.get_ofFn]
    exact hjoin ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right (W.mu+W.bridgeLength) K)⟩

end RiffleLowerV2.Localization
