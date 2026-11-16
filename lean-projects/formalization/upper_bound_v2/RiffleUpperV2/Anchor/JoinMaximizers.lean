import RiffleUpperV2.Anchor.UnequalQuantitative
import RiffleUpperV2.Anchor.EqualVariance
import RiffleUpperV2.Shared.SideMass

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Anchor
open TimeProfile RiffleUpperV2.Localization

def extendIndex {k d : ℕ} {v x : Prefix k d} (hvx : IsPrefix v x) (i : Fin v.1.val) : Fin x.1.val :=
  Fin.castLE (prefix_length_le hvx) i

theorem prefix_digit_eq {k d : ℕ} {v x : Prefix k d} (hvx : IsPrefix v x) (i : Fin v.1.val) :
    v.2.get i = x.2.get (extendIndex hvx i) := by
  simpa only [List.Vector.get, List.Vector.toList, Fin.cast, List.get_eq_getElem,
    extendIndex, Fin.castLE] using hvx.getElem (by simpa using i.isLt)

theorem prefixColumn_extend {k d : ℕ} {v x : Prefix k d} (hvx : IsPrefix v x) (i : Fin v.1.val) :
    prefixColumn x (extendIndex hvx i) = prefixColumn v i := by
  apply Fin.ext
  rfl

theorem sidePrefixMass_extension {k n d : ℕ} (cuts : Cuts k n d) {v x : Prefix k d}
    (hvx : IsPrefix v x) (i : Fin v.1.val) :
    sidePrefixMass cuts x (extendIndex hvx i) = sidePrefixMass cuts v i := by
  unfold sidePrefixMass
  apply Finset.prod_congr rfl
  intro t _
  let tv : Fin v.1.val := ⟨t.val, lt_trans t.isLt i.isLt⟩
  have he := prefix_digit_eq hvx tv
  have hc := prefixColumn_extend hvx tv
  change digitProbability cuts (prefixColumn x (extendIndex hvx tv)) (x.2.get (extendIndex hvx tv)) =
    digitProbability cuts (prefixColumn v tv) (v.2.get tv)
  rw [hc, ← he]

/-- Side means at join digits remain exactly unchanged under every extension,
including the extension of length zero x=v. -/
theorem sideMeans_extension {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    {v x : Prefix k d} (hvx : IsPrefix v x) (i : Fin v.1.val) :
    leftMean cuts R x (extendIndex hvx i) = leftMean cuts R v i ∧
    rightMean cuts R x (extendIndex hvx i) = rightMean cuts R v i := by
  unfold leftMean rightMean
  rw [sidePrefixMass_extension cuts hvx i, prefixColumn_extend hvx i, ← prefix_digit_eq hvx i]
  exact ⟨rfl,rfl⟩

theorem leftScale_attained {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) (hpos : 0 < leftScale cuts R v) :
    ∃ i : Fin v.1.val, leftMean cuts R v i = leftScale cuts R v := by
  obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup'
    (s := insert 0 (Finset.univ.image (leftMean cuts R v))) (by simp) id
  change leftScale cuts R v = a at he
  rcases Finset.mem_insert.mp ha with hzero | him
  · subst a
    linarith
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp him
    exact ⟨i,hi.trans he.symm⟩

theorem rightScale_attained {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) (hpos : 0 < rightScale cuts R v) :
    ∃ i : Fin v.1.val, rightMean cuts R v i = rightScale cuts R v := by
  obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup'
    (s := insert 0 (Finset.univ.image (rightMean cuts R v))) (by simp) id
  change rightScale cuts R v = a at he
  rcases Finset.mem_insert.mp ha with hzero | him
  · subst a
    linarith
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp him
    exact ⟨i,hi.trans he.symm⟩

/-- Genuine post-anchor boundaries supply positive, attained extrema at join
digits, transported exactly into any continuation x. -/
theorem genuine_continuation_maximizers {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) {χ : ℝ} {y z v x : Prefix k d}
    (h : GenuineBoundaryPair cuts R χ y z v) (hvx : IsPrefix v x) :
    0 < leftScale cuts R v ∧ 0 < rightScale cuts R v ∧
      ∃ i j : Fin x.1.val,
        leftMean cuts R x i = leftScale cuts R v ∧ rightMean cuts R x j = rightScale cuts R v := by
  have hs := genuine_sideScale_pos cuts hn R h
  have hl : 0 < leftScale cuts R v := hs.1.trans_le (hs.2.trans (min_le_left _ _))
  have hr : 0 < rightScale cuts R v := hs.1.trans_le (hs.2.trans (min_le_right _ _))
  obtain ⟨i,hi⟩ := leftScale_attained cuts R v hl
  obtain ⟨j,hj⟩ := rightScale_attained cuts R v hr
  exact ⟨hl,hr,extendIndex hvx i,extendIndex hvx j,
    (sideMeans_extension cuts R hvx i).1.trans hi, (sideMeans_extension cuts R hvx j).2.trans hj⟩

theorem varianceDenominator_gt_one {k d : ℕ} {χ : ℝ} (v : Prefix k d)
    (hχ : 0 < χ) (hχ1 : χ < 1) : 1 < varianceDenominator χ v := by
  have hi : 1 < χ⁻¹ := (one_lt_inv₀ hχ).mpr hχ1
  unfold varianceDenominator
  linarith [(Nat.cast_nonneg v.1.val : (0 : ℝ) ≤ v.1.val)]

end RiffleUpperV2.Anchor
