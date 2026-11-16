import RiffleLowerV2.Localization.WordOrder
import RiffleLowerV2.Thinning.MaximalWord
import RiffleLowerV2.Types.MassBins

noncomputable section
open scoped BigOperators NNReal
open Set
namespace RiffleLowerV2.Localization
open TimeProfile

@[simp] theorem mem_columnSet {K a b : ℕ} {j : Fin K} :
    j ∈ columnSet K a b ↔ a ≤ j.val ∧ j.val < b := by
  simp [columnSet]

theorem columnSet_card {K a b : ℕ} (hab : a ≤ b) (hb : b ≤ K) :
    (columnSet K a b).card = b-a := by
  let e : columnSet K a b ≃ Fin (b-a) :=
    { toFun := fun j => ⟨j.val.val-a, by
        have hj := mem_columnSet.mp j.property
        omega⟩
      invFun := fun j => ⟨⟨a+j.val, by omega⟩, mem_columnSet.mpr (by dsimp; omega)⟩
      left_inv := by intro j; apply Subtype.ext; apply Fin.ext
                     have hj := mem_columnSet.mp j.property
                     simp only
                     omega
      right_inv := by intro j; apply Fin.ext; simp }
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr e

theorem columnSet_union {K a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    columnSet K a b ∪ columnSet K b c = columnSet K a c := by
  ext j
  simp only [Finset.mem_union, mem_columnSet]
  omega

theorem columnSet_disjoint {K a b c : ℕ} :
    Disjoint (columnSet K a b) (columnSet K b c) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  have h := mem_columnSet.mp hj
  have h' := mem_columnSet.mp hk
  omega

theorem prod_columnSet_split {K a b c : ℕ} (f : Fin K → ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∏ j ∈ columnSet K a c, f j) =
      (∏ j ∈ columnSet K a b, f j) * ∏ j ∈ columnSet K b c, f j := by
  rw [← columnSet_union hab hbc, Finset.prod_union columnSet_disjoint]

theorem massOn_restrictWord {k N K : ℕ} (cuts : Cuts k N K)
    (I : Finset (Fin K)) (w : Word k K) :
    massOn cuts (restrictWord I w) = ∏ j ∈ I, (cuts.count j (w.get j) : ℝ)/N := by
  unfold massOn restrictWord
  exact Finset.prod_coe_sort I (fun j : Fin K => (cuts.count j (w.get j) : ℝ)/N)

theorem prefixMass_split {k N K a b : ℕ} (cuts : Cuts k N K)
    (w : Word k K) (hab : a ≤ b) (hb : b ≤ K) :
    prefixMass cuts (prefixAt b w) = prefixMass cuts (prefixAt a w) *
      massOn cuts (restrictWord (columnSet K a b) w) := by
  rw [prefixMass_prefixAt_eq_prod cuts b w hb,
    prefixMass_prefixAt_eq_prod cuts a w (hab.trans hb), massOn_restrictWord,
    prod_columnSet_split _ (Nat.zero_le a) hab]

@[simp] theorem joinColdWord_get_prefix {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W))
    (z : WordOn k (tailColumns K W)) (j : prefixColumns K W) :
    (joinColdWord G x v z).get j.val = x j := by
  simp [joinColdWord, j.property]

@[simp] theorem joinColdWord_get_bridge {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W))
    (z : WordOn k (tailColumns K W)) (j : bridgeColumns K W) :
    (joinColdWord G x v z).get j.val = v j := by
  have hj := mem_columnSet.mp j.property
  have hn : j.val ∉ prefixColumns K W := by
    simp only [prefixColumns, mem_columnSet]
    omega
  simp [joinColdWord, hn, j.property]

@[simp] theorem joinColdWord_get_tail {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W))
    (z : WordOn k (tailColumns K W)) (j : tailColumns K W) :
    (joinColdWord G x v z).get j.val = z j := by
  have hj := mem_columnSet.mp j.property
  have hn : j.val ∉ prefixColumns K W := by
    simp only [prefixColumns, mem_columnSet]
    omega
  have hn' : j.val ∉ bridgeColumns K W := by
    simp only [bridgeColumns, mem_columnSet]
    omega
  simp [joinColdWord, hn, hn', j.property]

theorem joinColdWord_get_ambient {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (hW : W.ms ≤ W.mu) (x : WordOn k (prefixColumns K W))
    (v : WordOn k (bridgeColumns K W)) (z : WordOn k (tailColumns K W))
    (j : Fin K) (hj : j.val < W.ms) :
    (joinColdWord G x v z).get j = G.ambient.get j := by
  have hp : j ∉ prefixColumns K W := by simp only [prefixColumns,mem_columnSet]; omega
  have hb : j ∉ bridgeColumns K W := by simp only [bridgeColumns,mem_columnSet]; omega
  have ht : j ∉ tailColumns K W := by simp only [tailColumns,mem_columnSet]; omega
  simp [joinColdWord,hp,hb,ht]

@[simp] theorem restrict_join_prefix {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W))
    (z : WordOn k (tailColumns K W)) :
    restrictWord (prefixColumns K W) (joinColdWord G x v z) = x := by
  funext j
  exact joinColdWord_get_prefix G x v z j

@[simp] theorem restrict_join_bridge {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W))
    (z : WordOn k (tailColumns K W)) :
    restrictWord (bridgeColumns K W) (joinColdWord G x v z) = v := by
  funext j
  exact joinColdWord_get_bridge G x v z j

@[simp] theorem restrict_join_tail {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W))
    (z : WordOn k (tailColumns K W)) :
    restrictWord (tailColumns K W) (joinColdWord G x v z) = z := by
  funext j
  exact joinColdWord_get_tail G x v z j

theorem prefixAt_joinColdWord {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (hW : W.ms ≤ W.mu) (hK : W.mu+W.bridgeLength ≤ K)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W))
    (z : WordOn k (tailColumns K W)) :
    prefixAt W.ms (joinColdWord G x v z) = prefixAt W.ms G.ambient := by
  apply prefixAt_eq_of_get (by omega)
  exact joinColdWord_get_ambient G hW x v z

theorem joinColdWord_injective {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (v : WordOn k (bridgeColumns K W)) :
    Function.Injective (fun xz : WordOn k (prefixColumns K W) × WordOn k (tailColumns K W) =>
      joinColdWord G xz.1 v xz.2) := by
  intro xz xz' heq
  apply Prod.ext
  · simpa using congrArg (restrictWord (prefixColumns K W)) heq
  · simpa using congrArg (restrictWord (tailColumns K W)) heq

theorem coldFullFamily_card {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) :
    (coldFullFamily cuts hN P W G).card =
      (coldPrefixFamily cuts hN P W G).card * (coldTailFamily cuts hN P W G).card := by
  classical
  rw [coldFullFamily, Finset.card_image_of_injective _ (joinColdWord_injective G G.central)]
  simp only [Finset.product_eq_sprod, Finset.card_product]

theorem reservePrefix_mean {k N K : ℕ} (cuts : Cuts k N K)
    {P : BorelPartition k} {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (hW : W.ms ≤ W.mu) (hK : W.mu+W.bridgeLength ≤ K)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W)) :
    prefixMean cuts (reservePrefix G x v) =
      prefixMean cuts (prefixAt W.ms G.ambient) * massOn cuts x * massOn cuts v := by
  let z := restrictWord (tailColumns K W) G.ambient
  have h1 := prefixMass_split cuts (joinColdWord G x v z) hW (by omega : W.mu ≤ K)
  have h2 := prefixMass_split cuts (joinColdWord G x v z)
    (Nat.le_add_right W.mu W.bridgeLength) hK
  rw [show columnSet K W.ms W.mu = prefixColumns K W from rfl,
    restrict_join_prefix, prefixAt_joinColdWord G hW hK] at h1
  rw [show columnSet K W.mu (W.mu+W.bridgeLength) = bridgeColumns K W from rfl,
    restrict_join_bridge, h1] at h2
  change (N : ℝ) * prefixMass cuts (prefixAt (W.mu+W.bridgeLength)
    (joinColdWord G x v z)) = _
  rw [h2]
  simp only [prefixMean]
  ring

theorem joinColdWord_mass {k N K : ℕ} (cuts : Cuts k N K)
    {P : BorelPartition k} {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (hW : W.ms ≤ W.mu) (hK : W.mu+W.bridgeLength ≤ K)
    (x : WordOn k (prefixColumns K W)) (v : WordOn k (bridgeColumns K W))
    (z : WordOn k (tailColumns K W)) :
    wordMass cuts (joinColdWord G x v z) =
      prefixMass cuts (prefixAt W.ms G.ambient) * massOn cuts x * massOn cuts v *
        massOn cuts z := by
  have h1 := prefixMass_split cuts (joinColdWord G x v z) hW (by omega : W.mu ≤ K)
  have h2 := prefixMass_split cuts (joinColdWord G x v z)
    (Nat.le_add_right W.mu W.bridgeLength) hK
  have h3 := prefixMass_split cuts (joinColdWord G x v z) hK (le_refl K)
  rw [show columnSet K W.ms W.mu = prefixColumns K W from rfl,
    restrict_join_prefix, prefixAt_joinColdWord G hW hK] at h1
  rw [show columnSet K W.mu (W.mu+W.bridgeLength) = bridgeColumns K W from rfl,
    restrict_join_bridge, h1] at h2
  rw [show columnSet K (W.mu+W.bridgeLength) K = tailColumns K W from rfl,
    restrict_join_tail, h2] at h3
  rw [prefixMass_prefixAt_eq_prod cuts K (joinColdWord G x v z) (le_refl K)] at h3
  have hs : columnSet K 0 K = Finset.univ := by
    ext j
    simp [columnSet]
  rw [hs] at h3
  exact h3

/-- The maximizing-coordinate argument is adapted from LB02 MaximalWord. -/
theorem canonical_digit_eq_pileMax {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (w : Word k K) (hw : IsCanonicalMaxWord cuts w) (j : Fin K) :
    (cuts.count j (w.get j) : ℝ)/N = pileMax (cuts.profile hN j) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_antisymm
  · exact prob_le_pileMax (cuts.profile hN j) (w.get j)
  · unfold pileMax
    have hp : ∀ l, prob (cuts.profile hN j) l ≤ (cuts.count j (w.get j) : ℝ)/N := by
      intro l
      exact div_le_div_of_nonneg_right (by exact_mod_cast (hw j).1 l) hNr.le
    exact_mod_cast (Finset.sup_le (s := Finset.univ)
      (f := fun l : Fin k => (⟨prob (cuts.profile hN j) l, prob_nonneg _ _⟩ : ℝ≥0))
      (a := (⟨(cuts.count j (w.get j) : ℝ)/N, by positivity⟩ : ℝ≥0))
      (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) =>
        (show (⟨prob (cuts.profile hN j) l, prob_nonneg _ _⟩ : ℝ≥0) ≤
          (⟨(cuts.count j (w.get j) : ℝ)/N, by positivity⟩ : ℝ≥0) from hp l)))

theorem canonical_digit_ge_inv {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (hk : 0 < k) (w : Word k K) (hw : IsCanonicalMaxWord cuts w) (j : Fin K) :
    1/(k : ℝ) ≤ (cuts.count j (w.get j) : ℝ)/N := by
  rw [canonical_digit_eq_pileMax cuts hN w hw j]
  exact inv_card_le_pileMax hk _

theorem canonical_prefixMean_eq_rpow_beta {k N K : ℕ} (cuts : Cuts k N K)
    (hN2 : 2 ≤ N) (hN : 0 < N) (w : Word k K) (hw : IsCanonicalMaxWord cuts w)
    (m : ℕ) (hm : m ≤ K) :
    prefixMean cuts (prefixAt m w) = (N : ℝ)^(beta cuts hN (gridTime N m)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : logScale N ≠ 0 := (logScale_pos hN2).ne'
  have hp : 0 < ∏ j ∈ columnSet K 0 m, pileMax (cuts.profile hN j) :=
    Finset.prod_pos fun j _ => pileMax_pos _
  have hmass : prefixMass cuts (prefixAt m w) =
      ∏ j ∈ columnSet K 0 m, pileMax (cuts.profile hN j) := by
    rw [prefixMass_prefixAt_eq_prod cuts m w hm]
    exact Finset.prod_congr rfl (fun j _ => canonical_digit_eq_pileMax cuts hN w hw j)
  have hA : A cuts hN 0 (gridTime N m) =
      (∑ j ∈ columnSet K 0 m, maxCost (cuts.profile hN j))/logScale N := by
    have hg := empiricalIntegral_grid hN2 (fun j => maxCost (cuts.profile hN j))
      0 m (Nat.zero_le m)
    simpa [A, gridTime, gridSum, columnSet] using hg
  rw [prefixMean, hmass, Real.rpow_def_of_pos hNr]
  apply Real.log_injOn_pos (mul_pos hNr hp) (Real.exp_pos _)
  rw [Real.log_exp, Real.log_mul hNr.ne' hp.ne',
    Real.log_prod (fun j _ => (pileMax_pos (cuts.profile hN j)).ne')]
  rw [beta, hA]
  simp only [maxCost, digitCost, one_div, Real.log_inv, Finset.sum_neg_distrib]
  change _ = logScale N * _
  field_simp [hL]
  dsimp [logScale]
  ring

end RiffleLowerV2.Localization
