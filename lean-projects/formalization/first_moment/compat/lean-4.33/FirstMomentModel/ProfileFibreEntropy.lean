import FirstMomentModel.ProfileClasses
import FirstMoment.Entropy
import Mathlib.Data.Fintype.EquivFin

/-!
Exact entropy bounds for the actual fibres of the frozen profile encoder.
The fibre's fixed prefix and labeled exceptional positions are not free digits.
-/

namespace InhomogeneousShuffle.FirstMoment.Model

noncomputable section

def profileKeyCounts {K k qb qe c : ℕ}
    (key : ProfileKey K k qb qe (c * k)) : Fin c → Fin k → ℕ :=
  fun a l => (key.2.2.2.1 (finProdFinEquiv (a, l))).val

def ProfileFibre {D : Riffle.Model} {c : ℕ}
    (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4)
    (key : ProfileKey D.K D.k (boundaryBudget A)
      (exceptionalBudget A alpha) (c * D.k)) : Type :=
  {p : ProfileWord A good alpha // encodeProfile A cell good alpha route p = key}

variable {D : Riffle.Model} {c : ℕ}

theorem profileKeyCounts_encode
    (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4) (p : ProfileWord A good alpha) :
    profileKeyCounts (c := c) (encodeProfile A cell good alpha route p) =
      goodDigitCount A cell good p.val.1 p.val.2.1 p.val.2.2 := by
  funext a l
  simp only [profileKeyCounts, encodeProfile, Equiv.symm_apply_apply]

theorem profileFibre_finite
    (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4)
    (key : ProfileKey D.K D.k (boundaryBudget A)
      (exceptionalBudget A alpha) (c * D.k)) :
    Finite (ProfileFibre A cell good alpha route key) := by
  classical
  let F := ProfileFibre A cell good alpha route key
  have hlegal (p : F) : Riffle.Legal D p.val.val.2.2 :=
    (Riffle.stable_desc (Riffle.admissiblePair_rawPair p.val.property.1)
      p.val.property.2.1).1
  let f : F → (Fin D.K → Fin (D.k + 1)) := fun p i =>
    if hi : i.val < p.val.val.2.2.length then
      ⟨Riffle.digit p.val.val.2.2 i.val,
        Nat.lt_succ_of_lt ((hlegal p).2 _ hi).1⟩
    else ⟨D.k, Nat.lt_succ_self D.k⟩
  have hf : Function.Injective f := by
    intro p q hpq
    rcases encodeProfile_eq_data A cell good alpha route p.val q.val
        (p.property.trans q.property.symm) with
      ⟨hy, hz, hlen, _, _, _, _⟩
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext hy (Prod.ext hz ?_)
    apply List.ext_getElem hlen
    intro i hi hiq
    have hiK : i < D.K := hi.trans_le (hlegal p).1
    have heq := congrArg Fin.val (congrFun hpq ⟨i, hiK⟩)
    have hdigit : Riffle.digit p.val.val.2.2 i = Riffle.digit q.val.val.2.2 i := by
      simpa only [f, dif_pos hi, dif_pos hiq] using heq
    simpa only [Riffle.digit, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hiq, Option.getD_some] using hdigit
  exact Finite.of_injective f hf

theorem profileFibre_card_le_exp_entropy
    (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4)
    (key : ProfileKey D.K D.k (boundaryBudget A)
      (exceptionalBudget A alpha) (c * D.k)) :
    (Nat.card (ProfileFibre A cell good alpha route key) : ℝ) ≤
      Real.exp (typeEntropy (profileKeyCounts (c := c) key)) := by
  classical
  let F := ProfileFibre A cell good alpha route key
  by_cases hF : Nonempty F
  · obtain ⟨p₀⟩ := hF
    have hlegal (p : F) : Riffle.Legal D p.val.val.2.2 :=
      (Riffle.stable_desc (Riffle.admissiblePair_rawPair p.val.property.1)
        p.val.property.2.1).1
    let J : Finset (Fin D.K) := Finset.univ.filter (fun i =>
      (Riffle.join p₀.val.val.1 p₀.val.val.2.1).length ≤ i.val ∧
        i.val < p₀.val.val.2.2.length ∧
        i ∉ exceptionalPositions A good p₀.val.val.1 p₀.val.val.2.1 p₀.val.val.2.2)
    have hJ (p : F) (i : Fin D.K) : i ∈ J ↔
        (Riffle.join p.val.val.1 p.val.val.2.1).length ≤ i.val ∧
          i.val < p.val.val.2.2.length ∧ good i (Riffle.digit p.val.val.2.2 i.val) := by
      rcases encodeProfile_eq_data A cell good alpha route p.val p₀.val
          (p.property.trans p₀.property.symm) with
        ⟨hy, hz, hlen, _, hQ, _, _⟩
      constructor
      · intro hi
        rcases (Finset.mem_filter.mp hi).2 with ⟨hlo, hup, hnot⟩
        have hlo' : (Riffle.join p.val.val.1 p.val.val.2.1).length ≤ i.val := by
          simpa only [hy, hz] using hlo
        have hup' : i.val < p.val.val.2.2.length := by
          simpa only [hlen] using hup
        refine ⟨hlo', hup', ?_⟩
        by_contra hbad
        have hip : i ∈ exceptionalPositions A good p.val.val.1 p.val.val.2.1
            p.val.val.2.2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo', hup', hbad⟩
        exact hnot (hQ ▸ hip)
      · rintro ⟨hlo, hup, hgood⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
        · simpa only [hy, hz] using hlo
        · simpa only [hlen] using hup
        · intro hiQ
          have hip : i ∈ exceptionalPositions A good p.val.val.1 p.val.val.2.1
              p.val.val.2.2 := hQ.symm ▸ hiQ
          exact (Finset.mem_filter.mp hip).2.2.2 hgood
    let e : Fin J.card ≃ ↥J := J.equivFin.symm
    let cellJ : Fin J.card → Fin c := fun j => cell (e j).val
    let restriction : F → Fin J.card → Fin D.k := by
      intro p j
      have hj := (hJ p (e j).val).mp (e j).property
      exact ⟨Riffle.digit p.val.val.2.2 (e j).val.val,
        ((hlegal p).2 _ hj.2.1).1⟩
    have hcounts (p : F) (a : Fin c) (l : Fin D.k) :
        (Finset.univ.filter (fun j : Fin J.card =>
          cellJ j = a ∧ restriction p j = l)).card =
          goodDigitCount A cell good p.val.val.1 p.val.val.2.1 p.val.val.2.2 a l := by
      unfold goodDigitCount
      apply Finset.card_bij (fun j _ => (e j).val)
      · intro j hj
        rcases (Finset.mem_filter.mp hj).2 with ⟨hcell, hdigit⟩
        have hpos := (hJ p (e j).val).mp (e j).property
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hpos.1, hpos.2.1, hcell, ?_, hpos.2.2⟩
        exact congrArg Fin.val hdigit
      · intro j _ j' _ h
        exact e.injective (Subtype.ext h)
      · intro i hi
        rcases (Finset.mem_filter.mp hi).2 with ⟨hlo, hup, hcell, hdigit, hgood⟩
        have hiJ : i ∈ J := (hJ p i).mpr ⟨hlo, hup, hgood⟩
        refine ⟨e.symm ⟨i, hiJ⟩, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · change cell (e (e.symm ⟨i, hiJ⟩)).val = a
            simpa only [Equiv.apply_symm_apply] using hcell
          · apply Fin.ext
            change Riffle.digit p.val.val.2.2 (e (e.symm ⟨i, hiJ⟩)).val.val = l.val
            simpa only [Equiv.apply_symm_apply] using hdigit
        · exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hiJ⟩)
    have hmem (p : F) : restriction p ∈
        typeClass cellJ (profileKeyCounts (c := c) key) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro a l
      rw [hcounts p a l]
      have hc := congrArg
        (fun t : ProfileKey D.K D.k (boundaryBudget A)
            (exceptionalBudget A alpha) (c * D.k) =>
          profileKeyCounts (c := c) t a l) p.property
      simpa only [profileKeyCounts_encode] using hc
    have hinj : Function.Injective restriction := by
      intro p q hpq
      rcases encodeProfile_eq_data A cell good alpha route p.val q.val
          (p.property.trans q.property.symm) with
        ⟨hy, hz, hlen, _, _, hlabels, _⟩
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext hy (Prod.ext hz ?_)
      apply List.ext_getElem hlen
      intro i hi hiq
      have hiK : i < D.K := hi.trans_le (hlegal p).1
      let ii : Fin D.K := ⟨i, hiK⟩
      have hdigit : Riffle.digit p.val.val.2.2 i = Riffle.digit q.val.val.2.2 i := by
        by_cases hbefore : i < (Riffle.join p.val.val.1 p.val.val.2.1).length
        · have hpref := (Riffle.stable_desc
            (Riffle.admissiblePair_rawPair p.val.property.1) p.val.property.2.1).2
          have hqref := (Riffle.stable_desc
            (Riffle.admissiblePair_rawPair q.val.property.1) q.val.property.2.1).2
          have hqbefore : i < (Riffle.join q.val.val.1 q.val.val.2.1).length := by
            simpa only [hy, hz] using hbefore
          calc
            Riffle.digit p.val.val.2.2 i =
                Riffle.digit (Riffle.join p.val.val.1 p.val.val.2.1) i :=
              (Riffle.digit_prefix hpref hbefore).symm
            _ = Riffle.digit (Riffle.join q.val.val.1 q.val.val.2.1) i := by rw [hy, hz]
            _ = Riffle.digit q.val.val.2.2 i := Riffle.digit_prefix hqref hqbefore
        · have hlo : (Riffle.join p.val.val.1 p.val.val.2.1).length ≤ i :=
            Nat.le_of_not_gt hbefore
          by_cases hbad : ii ∈ exceptionalPositions A good p.val.val.1 p.val.val.2.1
              p.val.val.2.2
          · exact hlabels ii hbad
          · have hiJ : ii ∈ J := by
              apply (hJ p ii).mpr
              refine ⟨hlo, hi, ?_⟩
              by_contra hnotgood
              exact hbad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo, hi, hnotgood⟩)
            let j : Fin J.card := e.symm ⟨ii, hiJ⟩
            have heq := congrArg Fin.val (congrFun hpq j)
            change Riffle.digit p.val.val.2.2 (e j).val.val =
              Riffle.digit q.val.val.2.2 (e j).val.val at heq
            simpa only [j, Equiv.apply_symm_apply] using heq
      simpa only [Riffle.digit, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hiq, Option.getD_some] using hdigit
    let f : F → ↥(typeClass cellJ (profileKeyCounts (c := c) key)) :=
      fun p => ⟨restriction p, hmem p⟩
    have hf : Function.Injective f := by
      intro p q h
      exact hinj (congrArg Subtype.val h)
    have hcard : Nat.card F ≤ (typeClass cellJ (profileKeyCounts (c := c) key)).card := by
      have h := Nat.card_le_card_of_injective f hf
      have hright : Nat.card ↥(typeClass cellJ (profileKeyCounts (c := c) key)) =
          (typeClass cellJ (profileKeyCounts (c := c) key)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact h.trans_eq hright
    have hcardR : (Nat.card F : ℝ) ≤
        ((typeClass cellJ (profileKeyCounts (c := c) key)).card : ℝ) := by
      exact_mod_cast hcard
    have hk : 0 < D.k := lt_of_lt_of_le (by decide : 0 < 2) D.two_le_k
    exact hcardR.trans (type_class_card_le_exp_entropy hk cellJ (profileKeyCounts key))
  · letI : IsEmpty F := ⟨fun p => hF ⟨p⟩⟩
    have hzero : Nat.card (ProfileFibre A cell good alpha route key) = 0 :=
      Nat.card_of_isEmpty
    rw [hzero, Nat.cast_zero]
    exact (Real.exp_pos _).le

theorem profileFibre_card_le_rpow_entropy
    (A : Riffle.Setup D) (cell : Fin D.K → Fin c)
    (good : Fin D.K → ℕ → Prop) (alpha : ℝ)
    (route : ProfileWord A good alpha → Fin 4)
    (key : ProfileKey D.K D.k (boundaryBudget A)
      (exceptionalBudget A alpha) (c * D.k)) :
    (Nat.card (ProfileFibre A cell good alpha route key) : ℝ) ≤
      (D.N : ℝ) ^ (typeEntropy (profileKeyCounts (c := c) key) /
        Real.log (D.N : ℝ)) := by
  have hN : (1 : ℝ) < D.N := by exact_mod_cast D.one_lt_N
  have hlog : Real.log (D.N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hN)
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hN)]
  rw [mul_div_cancel₀ _ hlog]
  exact profileFibre_card_le_exp_entropy A cell good alpha route key

end

end InhomogeneousShuffle.FirstMoment.Model
