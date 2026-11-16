import RiffleLowerV2.Localization.Words
import RiffleLowerV2.Localization.Endpoints.Coordinates
import RiffleLowerV2.Localization.Intervals
import RiffleLowerV2.Model.Sorting

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Localization
open TimeProfile

theorem take_eq_map_finRange {k K m : ℕ} (hm : m ≤ K) (w : Word k K) :
    w.toList.take m = (List.finRange m).map
      (fun j : Fin m => w.get ⟨j.val, lt_of_lt_of_le j.isLt hm⟩) := by
  rw [← List.ofFn_eq_map]
  apply List.ext_getElem
  · simp [Nat.min_eq_left hm]
  · intro j hj hj'
    simp only [List.getElem_take,List.getElem_ofFn,List.Vector.get,
      List.get_eq_getElem,List.Vector.toList,Fin.val_cast]

theorem take_lt_take_iff {k K m : ℕ} (hm : m ≤ K) (v w : Word k K) :
    v.toList.take m < w.toList.take m ↔
      ∃ j : Fin K, j.val < m ∧ v.get j < w.get j ∧
        ∀ h : Fin K, h.val < j.val → v.get h = w.get h := by
  rw [take_eq_map_finRange hm v, take_eq_map_finRange hm w,
    map_lt_map_iff _ (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange m))]
  constructor
  · rintro ⟨j,hj,hlt,hpre⟩
    refine ⟨⟨j.val,lt_of_lt_of_le j.isLt hm⟩,j.isLt,hlt,?_⟩
    intro q hq
    change q.val < j.val at hq
    exact hpre ⟨q.val,by omega⟩ (by simp) hq
  · rintro ⟨j,hjm,hlt,hpre⟩
    refine ⟨⟨j.val,hjm⟩,by simp,hlt,?_⟩
    intro q _ hq
    exact hpre ⟨q.val,lt_of_lt_of_le q.isLt hm⟩ hq

theorem take_lt_split {k K l m : ℕ} (hlm : l ≤ m) (hm : m ≤ K) (v w : Word k K) :
    v.toList.take m < w.toList.take m ↔
      v.toList.take l < w.toList.take l ∨
      (v.toList.take l = w.toList.take l ∧
        wordOnList (restrictWord (columnSet K l m) v) <
          wordOnList (restrictWord (columnSet K l m) w)) := by
  rw [take_lt_take_iff hm]
  constructor
  · rintro ⟨j,hjm,hlt,hpre⟩
    by_cases hjl : j.val < l
    · exact Or.inl ((take_lt_take_iff (hlm.trans hm) v w).mpr ⟨j,hjl,hlt,hpre⟩)
    · refine Or.inr ⟨(take_eq_take_iff (hlm.trans hm) v w).mpr ?_,?_⟩
      · intro q hq; exact hpre q (by omega)
      · apply (wordOnList_lt_iff _ _).mpr
        refine ⟨⟨j,mem_columnSet.mpr ⟨by omega,hjm⟩⟩,hlt,?_⟩
        intro q hq
        exact hpre q.val hq
  · rintro (h | ⟨he,h⟩)
    · obtain ⟨j,hjl,hlt,hpre⟩ := (take_lt_take_iff (hlm.trans hm) v w).mp h
      exact ⟨j,lt_of_lt_of_le hjl hlm,hlt,hpre⟩
    · obtain ⟨j,hlt,hpre⟩ := (wordOnList_lt_iff _ _).mp h
      have hj := mem_columnSet.mp j.property
      refine ⟨j.val,hj.2,hlt,?_⟩
      intro q hq
      by_cases hql : q.val < l
      · exact (take_eq_take_iff (hlm.trans hm) v w).mp he q hql
      · exact hpre ⟨q,mem_columnSet.mpr ⟨by omega,by omega⟩⟩ hq

theorem take_le_split {k K l m : ℕ} (hlm : l ≤ m) (hm : m ≤ K) (v w : Word k K) :
    v.toList.take m ≤ w.toList.take m ↔
      v.toList.take l < w.toList.take l ∨
      (v.toList.take l = w.toList.take l ∧
        wordOnList (restrictWord (columnSet K l m) v) ≤
          wordOnList (restrictWord (columnSet K l m) w)) := by
  constructor
  · intro h
    have hpre : v.toList.take l ≤ w.toList.take l := by
      have h' := RiffleShuffle.take_lex_monotone l h
      simpa [List.take_take, Nat.min_eq_left hlm] using h'
    rcases lt_or_eq_of_le hpre with hlt | he
    · exact Or.inl hlt
    · refine Or.inr ⟨he,?_⟩
      apply le_of_not_gt
      intro hgt
      exact not_lt_of_ge h ((take_lt_split hlm hm w v).mpr (Or.inr ⟨he.symm,hgt⟩))
  · rintro (h | ⟨he,h⟩)
    · exact ((take_lt_split hlm hm v w).mpr (Or.inl h)).le
    · apply le_of_not_gt
      intro hgt
      rcases (take_lt_split hlm hm w v).mp hgt with hlt | ⟨_,hgt⟩
      · exact (not_lt_of_ge he.le) hlt
      · exact not_lt_of_ge h hgt

theorem lowerRank_prefixAt {k N K m : ℕ} {cuts : Cuts k N K}
    (hm : m ≤ K) (w : Word k K) (omega : Sample cuts) :
    lowerRank (prefixAt m w) omega =
      (Finset.univ.filter fun i => (rowWord omega i).toList.take m < w.toList.take m).card := by
  unfold lowerRank
  rw [prefixAt_toList _ _ hm]
  simp only [prefixAt,Nat.min_eq_left hm]

theorem upperRank_prefixAt {k N K m : ℕ} {cuts : Cuts k N K}
    (hm : m ≤ K) (w : Word k K) (omega : Sample cuts) :
    upperRank (prefixAt m w) omega =
      (Finset.univ.filter fun i => (rowWord omega i).toList.take m ≤ w.toList.take m).card := by
  unfold upperRank
  rw [prefixAt_toList _ _ hm]
  simp only [prefixAt,Nat.min_eq_left hm]

theorem relative_rank_decomposition {k N K l m : ℕ} {cuts : Cuts k N K}
    (hlm : l ≤ m) (hm : m ≤ K) (a w : Word k K)
    (x : WordOn k (columnSet K l m))
    (ha : w.toList.take l = a.toList.take l)
    (hx : restrictWord (columnSet K l m) w=x) (omega : Sample cuts) :
    lowerRank (prefixAt m w) omega = lowerRank (prefixAt l a) omega+
      relativeLowerCount a l m x omega ∧
    upperRank (prefixAt m w) omega = lowerRank (prefixAt l a) omega+
      relativeUpperCount a l m x omega := by
  let A := Finset.univ.filter fun i : Fin N => (rowWord omega i).toList.take l < a.toList.take l
  let B := Finset.univ.filter fun i : Fin N => (rowWord omega i).toList.take l = a.toList.take l ∧
    wordOnList (restrictWord (columnSet K l m) (rowWord omega i)) < wordOnList x
  let C := Finset.univ.filter fun i : Fin N => (rowWord omega i).toList.take l = a.toList.take l ∧
    wordOnList (restrictWord (columnSet K l m) (rowWord omega i)) ≤ wordOnList x
  have hdis (D : Finset (Fin N))
      (hD : ∀ i∈D, (rowWord omega i).toList.take l=a.toList.take l) : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact ((Finset.mem_filter.mp hi).2).ne (hD i hj)
  have hL : (Finset.univ.filter fun i : Fin N =>
      (rowWord omega i).toList.take m < w.toList.take m) = A∪B := by
    ext i
    simp only [A,B,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [take_lt_split hlm hm,ha,hx]
  have hU : (Finset.univ.filter fun i : Fin N =>
      (rowWord omega i).toList.take m ≤ w.toList.take m) = A∪C := by
    ext i
    simp only [A,C,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [take_le_split hlm hm,ha,hx]
  rw [lowerRank_prefixAt hm,upperRank_prefixAt hm,lowerRank_prefixAt (hlm.trans hm),hL,hU,
    Finset.card_union_of_disjoint (hdis B (fun i hi => (Finset.mem_filter.mp hi).2.1)),
    Finset.card_union_of_disjoint (hdis C (fun i hi => (Finset.mem_filter.mp hi).2.1))]
  exact ⟨rfl,rfl⟩

theorem sorted_take_lt_iff {k N K m : ℕ} {cuts : Cuts k N K}
    (hm : m ≤ K) (w : Word k K) (omega : Sample cuts) (i : Fin N) :
    i.val < lowerRank (prefixAt m w) omega ↔
      (sortedWord omega i).toList.take m < w.toList.take m := by
  let g : Fin N → List (Fin k) := fun j => (sortedWord omega j).toList.take m
  have hg : Monotone g := fun j q hjq =>
    RiffleShuffle.take_lex_monotone m (Tuple.monotone_sort (rowWord omega) hjq)
  have h := Tuple.lt_card_lt_iff_apply_lt_of_monotone (a := w.toList.take m) (j := i) hg
  convert h using 2
  rw [lowerRank_prefixAt hm]
  symm
  apply Finset.card_bij (fun j _ => stableSort omega j)
  · intro j hj
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,g,sortedWord] using hj
  · intro j _ q _ h; exact (stableSort omega).injective h
  · intro j hj
    refine ⟨(stableSort omega).symm j,?_,by simp⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,g,sortedWord,
      Equiv.apply_symm_apply] using hj

theorem sorted_take_le_iff {k N K m : ℕ} {cuts : Cuts k N K}
    (hm : m ≤ K) (w : Word k K) (omega : Sample cuts) (i : Fin N) :
    i.val < upperRank (prefixAt m w) omega ↔
      (sortedWord omega i).toList.take m ≤ w.toList.take m := by
  let g : Fin N → List (Fin k) := fun j => (sortedWord omega j).toList.take m
  have hg : Monotone g := fun j q hjq =>
    RiffleShuffle.take_lex_monotone m (Tuple.monotone_sort (rowWord omega) hjq)
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone (a := w.toList.take m) (j := i) hg
  convert h using 2
  rw [upperRank_prefixAt hm]
  symm
  apply Finset.card_bij (fun j _ => stableSort omega j)
  · intro j hj
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,g,sortedWord] using hj
  · intro j _ q _ h; exact (stableSort omega).injective h
  · intro j hj
    refine ⟨(stableSort omega).symm j,?_,by simp⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,g,sortedWord,
      Equiv.apply_symm_apply] using hj

theorem prefixCount_add_lowerRank {k N K : ℕ} (cuts : Cuts k N K)
    (w : Prefix k K) (omega : Sample cuts) :
    lowerRank w omega+prefixCount w omega=upperRank w omega := by
  have hle : lowerRank w omega ≤ upperRank w omega := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.le⟩
  have hd := (Model.prefixRanks cuts omega w).2
  omega

theorem prefix_rank_bounds_of_take_eq {k N K l m : ℕ} {cuts : Cuts k N K}
    (hlm : l ≤ m) (hm : m ≤ K) (a w : Word k K)
    (he : w.toList.take l=a.toList.take l) (omega : Sample cuts) :
    lowerRank (prefixAt l a) omega ≤ lowerRank (prefixAt m w) omega ∧
    upperRank (prefixAt m w) omega ≤ upperRank (prefixAt l a) omega := by
  rw [lowerRank_prefixAt (hlm.trans hm),lowerRank_prefixAt hm,
    upperRank_prefixAt hm,upperRank_prefixAt (hlm.trans hm)]
  constructor
  · apply Finset.card_le_card
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(take_lt_split hlm hm _ _).mpr (Or.inl ?_)⟩
    simpa only [he] using (Finset.mem_filter.mp hi).2
  · apply Finset.card_le_card
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases (take_le_split hlm hm _ _).mp (Finset.mem_filter.mp hi).2 with h | ⟨h,_⟩
    · simpa only [he] using h.le
    · simpa only [he] using h.le

theorem joinColdWord_take_mu_eq {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (hW : W.ms ≤ W.mu) (hK : W.mu+W.bridgeLength ≤ K)
    (x : WordOn k (prefixColumns K W))
    (v v' : WordOn k (bridgeColumns K W)) (z z' : WordOn k (tailColumns K W)) :
    (joinColdWord G x v z).toList.take W.mu=(joinColdWord G x v' z').toList.take W.mu := by
  apply (take_eq_take_iff (by omega) _ _).mpr
  intro j hj
  by_cases hjs : j.val<W.ms
  · rw [joinColdWord_get_ambient G hW x v z j hjs,
      joinColdWord_get_ambient G hW x v' z' j hjs]
  · have hjp : j∈prefixColumns K W := mem_columnSet.mpr ⟨by omega,hj⟩
    exact (joinColdWord_get_prefix G x v z ⟨j,hjp⟩).trans
      (joinColdWord_get_prefix G x v' z' ⟨j,hjp⟩).symm

theorem joinColdWord_bridge_lt {k K : ℕ} {P : BorelPartition k}
    {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (hW : W.ms ≤ W.mu) (hK : W.mu+W.bridgeLength ≤ K)
    (x : WordOn k (prefixColumns K W))
    (v v' : WordOn k (bridgeColumns K W)) (z z' : WordOn k (tailColumns K W))
    (hv : wordOnList v < wordOnList v') :
    (joinColdWord G x v z).toList.take (W.mu+W.bridgeLength) <
      (joinColdWord G x v' z').toList.take (W.mu+W.bridgeLength) := by
  apply (take_lt_split (Nat.le_add_right W.mu W.bridgeLength) hK _ _).mpr
  refine Or.inr ⟨joinColdWord_take_mu_eq G hW hK x v v' z z',?_⟩
  change wordOnList (restrictWord (bridgeColumns K W) (joinColdWord G x v z)) <
    wordOnList (restrictWord (bridgeColumns K W) (joinColdWord G x v' z'))
  simpa using hv

theorem coldWord_rank_barriers {k N K : ℕ} {cuts : Cuts k N K}
    {P : BorelPartition k} {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (hW : W.ms ≤ W.mu) (hK : W.mu+W.bridgeLength ≤ K)
    (hminus : wordOnList G.reserveMinus < wordOnList G.central)
    (hplus : wordOnList G.central < wordOnList G.reservePlus)
    (x : WordOn k (prefixColumns K W)) (z : WordOn k (tailColumns K W))
    (omega : Sample cuts) (i : Fin N) (hi : sortedWord omega i=joinColdWord G x G.central z) :
    lowerRank (prefixAt W.ms G.ambient) omega+
      relativeLowerCount G.ambient W.ms W.mu x omega+
      prefixCount (reservePrefix G x G.reserveMinus) omega ≤ i.val ∧
    i.val+1+prefixCount (reservePrefix G x G.reservePlus) omega ≤
      lowerRank (prefixAt W.ms G.ambient) omega+
        relativeUpperCount G.ambient W.ms W.mu x omega := by
  let y := joinColdWord G x G.central z
  let z0 := restrictWord (tailColumns K W) G.ambient
  let ym := joinColdWord G x G.reserveMinus z0
  let yp := joinColdWord G x G.reservePlus z0
  have hmu : W.mu ≤ K := by omega
  have hya : y.toList.take W.ms=G.ambient.toList.take W.ms := by
    apply (take_eq_take_iff (by omega) _ _).mpr
    exact joinColdWord_get_ambient G hW x G.central z
  have hrel := relative_rank_decomposition hW hmu G.ambient y x hya
    (restrict_join_prefix G x G.central z) omega
  have hmcmp : ym.toList.take (W.mu+W.bridgeLength)<y.toList.take (W.mu+W.bridgeLength) :=
    joinColdWord_bridge_lt G hW hK x G.reserveMinus G.central z0 z hminus
  have hpcmp : y.toList.take (W.mu+W.bridgeLength)<yp.toList.take (W.mu+W.bridgeLength) :=
    joinColdWord_bridge_lt G hW hK x G.central G.reservePlus z z0 hplus
  have hmrank : upperRank (prefixAt (W.mu+W.bridgeLength) ym) omega ≤ i.val := by
    apply Nat.le_of_not_gt
    intro h
    have ht := (sorted_take_le_iff hK ym omega i).mp h
    rw [hi] at ht
    exact not_le_of_gt hmcmp ht
  have hprank : i.val+1 ≤ lowerRank (prefixAt (W.mu+W.bridgeLength) yp) omega := by
    have ht : i.val < lowerRank (prefixAt (W.mu+W.bridgeLength) yp) omega :=
      (sorted_take_lt_iff hK yp omega i).mpr (by simpa only [hi] using hpcmp)
    omega
  have hmext := (prefix_rank_bounds_of_take_eq (Nat.le_add_right W.mu W.bridgeLength) hK y ym
    (joinColdWord_take_mu_eq G hW hK x G.reserveMinus G.central z0 z) omega).1
  have hpext := (prefix_rank_bounds_of_take_eq (Nat.le_add_right W.mu W.bridgeLength) hK y yp
    (joinColdWord_take_mu_eq G hW hK x G.reservePlus G.central z0 z) omega).2
  have hmc := prefixCount_add_lowerRank cuts (prefixAt (W.mu+W.bridgeLength) ym) omega
  have hpc := prefixCount_add_lowerRank cuts (prefixAt (W.mu+W.bridgeLength) yp) omega
  change lowerRank (prefixAt W.ms G.ambient) omega+
    relativeLowerCount G.ambient W.ms W.mu x omega+
    prefixCount (prefixAt (W.mu+W.bridgeLength) ym) omega ≤ i.val ∧
    i.val+1+prefixCount (prefixAt (W.mu+W.bridgeLength) yp) omega ≤
      lowerRank (prefixAt W.ms G.ambient) omega+relativeUpperCount G.ambient W.ms W.mu x omega
  omega

theorem coldWord_mem_translate {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    {P : BorelPartition k} {W : ColdWitnessData} (G : ColdGeometryData K P W)
    (hW : W.ms ≤ W.mu) (hK : W.mu+W.bridgeLength ≤ K)
    (hminus : wordOnList G.reserveMinus < wordOnList G.central)
    (hplus : wordOnList G.central < wordOnList G.reservePlus)
    (x : WordOn k (prefixColumns K W)) (hx : x∈coldPrefixFamily cuts hN P W G)
    (z : WordOn k (tailColumns K W)) (e : ℝ) (omega : Sample cuts)
    (hL : |(relativeLowerCount G.ambient W.ms W.mu x omega : ℝ)-
      prefixMean cuts (prefixAt W.ms G.ambient)*relativeMassBefore cuts x| ≤ e)
    (hU : |(relativeUpperCount G.ambient W.ms W.mu x omega : ℝ)-
      prefixMean cuts (prefixAt W.ms G.ambient)*(relativeMassBefore cuts x+massOn cuts x)| ≤ e)
    (hCm : e+2 ≤ (prefixCount (reservePrefix G x G.reserveMinus) omega : ℝ))
    (hCp : e+2 ≤ (prefixCount (reservePrefix G x G.reservePlus) omega : ℝ))
    (i : Fin N) (hi : sortedWord omega i=joinColdWord G x G.central z) :
    i∈clipTranslate N (coldRelativeSet cuts hN P W G)
      (lowerRank (prefixAt W.ms G.ambient) omega : ℤ) := by
  have hb := coldWord_rank_barriers G hW hK hminus hplus x z omega i hi
  have hbL : (lowerRank (prefixAt W.ms G.ambient) omega : ℝ)+
      relativeLowerCount G.ambient W.ms W.mu x omega+
      prefixCount (reservePrefix G x G.reserveMinus) omega ≤ (i.val : ℝ) := by
    exact_mod_cast hb.1
  have hbU : (i.val : ℝ)+1+prefixCount (reservePrefix G x G.reservePlus) omega ≤
      (lowerRank (prefixAt W.ms G.ambient) omega : ℝ)+
        relativeUpperCount G.ambient W.ms W.mu x omega := by
    exact_mod_cast hb.2
  rw [mem_clipTranslate]
  apply Finset.mem_biUnion.mpr
  refine ⟨x,hx,(mem_integerHalfOpen _ _ _).mpr ?_⟩
  have hc : ((manuscriptRank i-(lowerRank (prefixAt W.ms G.ambient) omega : ℤ) : ℤ) : ℝ) =
      (i.val : ℝ)+1-(lowerRank (prefixAt W.ms G.ambient) omega : ℝ) := by
    simp [manuscriptRank]
  rw [hc]
  constructor
  · linarith [(abs_le.mp hL).1]
  · linarith [(abs_le.mp hU).2]

/-- Endpoint control and the two actual reserve counts localize every tail on one sample. -/
theorem coldFamily_localized_of_endpoint_reserves {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) {P : BorelPartition k} {W : ColdWitnessData}
    (G : ColdGeometryData K P W) (hW : W.ms ≤ W.mu)
    (hK : W.mu+W.bridgeLength ≤ K)
    (hminus : wordOnList G.reserveMinus < wordOnList G.central)
    (hplus : wordOnList G.central < wordOnList G.reservePlus)
    (e : ℝ) (omega : Sample cuts)
    (hbounds : ∀ x∈coldPrefixFamily cuts hN P W G,
      |(relativeLowerCount G.ambient W.ms W.mu x omega : ℝ)-
        prefixMean cuts (prefixAt W.ms G.ambient)*relativeMassBefore cuts x| ≤ e ∧
      |(relativeUpperCount G.ambient W.ms W.mu x omega : ℝ)-
        prefixMean cuts (prefixAt W.ms G.ambient)*(relativeMassBefore cuts x+massOn cuts x)| ≤ e ∧
      e+2 ≤ (prefixCount (reservePrefix G x G.reserveMinus) omega : ℝ) ∧
      e+2 ≤ (prefixCount (reservePrefix G x G.reservePlus) omega : ℝ)) :
    ∀ y∈coldFullFamily cuts hN P W G, ∀ i : Fin N, sortedWord omega i=y →
      i∈clipTranslate N (coldRelativeSet cuts hN P W G)
        (lowerRank (prefixAt W.ms G.ambient) omega : ℤ) := by
  intro y hy i hi
  rcases Finset.mem_image.mp hy with ⟨xz,hxz,rfl⟩
  have hx : xz.1∈coldPrefixFamily cuts hN P W G := by
    rw [Finset.product_eq_sprod] at hxz
    exact (Finset.mem_product.mp hxz).1
  rcases hbounds xz.1 hx with ⟨hL,hU,hCm,hCp⟩
  exact coldWord_mem_translate cuts hN G hW hK hminus hplus xz.1 hx xz.2 e omega
    hL hU hCm hCp i hi

end RiffleLowerV2.Localization
