import RiffleUpperV2.Localization.RestrictedMoments
import RiffleUpperV2.Localization.CylinderAdapters

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open TimeProfile Anchor RiffleLowerV2.Factorial

/-- Squared word masses among full future words extending the stopped prefix. -/
def extensionSquareMass {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d) : ℝ :=
  ∑ w : Word k d, if w.toList.take x.1.val = x.2.toList then
    RiffleLowerV2.wordMass cuts w ^ 2 else 0

/-- Future collision product, with the exposed prefix and fixed anchor excluded. -/
def tailSquareMass {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d) : ℝ :=
  ∏ j : Fin d, if j.val < x.1.val then 1 else
    ∑ a : Fin k, ((cuts.count j a : ℝ)/n)^2

theorem historyWordRows_internal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) (w : Word k d) :
    historyWordRows (internalHistory R x ω) w.get =
      if w.toList.take x.1.val = x.2.toList then R.filter (fun r => rowWord ω r=w) else ∅ := by
  have he (r : Fin n) : (fun j => sampleEntry ω r j) = w.get ↔ rowWord ω r=w := by
    constructor
    · intro h
      apply List.Vector.ext
      intro j
      exact (RiffleLowerV2.rowWord_get ω r j).trans (congrFun h j)
    · intro h
      funext j
      exact (RiffleLowerV2.rowWord_get ω r j).symm.trans (congrArg (fun v : Word k d => v.get j) h)
  ext r
  simp only [historyWordRows, Finset.mem_filter, Finset.mem_univ, true_and, internalHistory]
  by_cases hw : w.toList.take x.1.val = x.2.toList
  · simp only [if_pos hw, Finset.mem_filter]
    by_cases hr : r ∈ prefixRows R x ω
    · rw [if_pos hr,Option.some.injEq,he]
      exact ⟨fun h => ⟨(Finset.mem_filter.mp hr).1,h⟩,fun h => h.2⟩
    · rw [if_neg hr]
      simp only [reduceCtorEq,false_iff,not_and]
      intro hR hrow
      apply hr
      exact Finset.mem_filter.mpr ⟨hR,by simpa only [hrow] using hw⟩
  · simp only [if_neg hw,show (r ∈ (∅ : Finset (Fin n))) ↔ False by simp,iff_false]
    by_cases hr : r ∈ prefixRows R x ω
    · rw [if_pos hr,Option.some.injEq,he]
      intro hrow
      exact hw (by simpa only [hrow] using (Finset.mem_filter.mp hr).2)
    · simp [hr]

theorem internalOffsets_card_le_pairs {k n d : ℕ} (u : InternalHistory k n d) :
    ((internalOffsets u).card : ℝ) ≤
      ∑ w : Word k d, ((historyWordRows u w.get).card.choose 2 : ℝ) := by
  have hs := (Equiv.vectorEquivFin (Fin k) d).sum_comp
    (fun w : Fin d → Fin k => ((historyWordRows u w).card.choose 2 : ℝ))
  change (∑ w : Word k d, ((historyWordRows u w.get).card.choose 2 : ℝ)) = _ at hs
  rw [hs]
  have hb := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin d → Fin k)))
    (t := fun w => Finset.Ico ((historyLessRows u w).card : ℤ)
      ((historyLessRows u w).card+(historyWordRows u w).card-1))
  have hb' : ((internalOffsets u).card : ℝ) ≤
      ∑ w : Fin d → Fin k, ((Finset.Ico ((historyLessRows u w).card : ℤ)
        ((historyLessRows u w).card+(historyWordRows u w).card-1)).card : ℝ) := by
    exact_mod_cast hb
  apply hb'.trans
  apply Finset.sum_le_sum
  intro w _
  rw [Int.card_Ico]
  have hi : (((historyLessRows u w).card : ℤ)+(historyWordRows u w).card-1)-
      (historyLessRows u w).card = (historyWordRows u w).card-1 := by omega
  rw [hi]
  generalize (historyWordRows u w).card = c
  rcases c with _ | c
  · norm_num
  · have hn : (((c+1 : ℕ):ℤ)-1).toNat=c := by omega
    rw [hn,Nat.cast_choose_two]
    push_cast
    have hc : (0:ℝ) ≤ c := Nat.cast_nonneg _
    by_cases hz : c=0
    · simp [hz]
    · have hc1 : (1:ℝ) ≤ c := by exact_mod_cast (show 1≤c by omega)
      nlinarith [sq_nonneg ((c:ℝ)-1)]

theorem expected_anchoredEdges_le_collisionMass {k n d : ℕ} (cuts : Cuts k n d)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) :
    expect (fixedCountPMF cuts) (fun ω => ((anchoredEdges c₀ R x ω).card : ℝ)) ≤
      (R.card.choose 2 : ℝ)*extensionSquareMass cuts x := by
  calc
    _ ≤ expect (fixedCountPMF cuts) (fun ω =>
      ∑ w : Word k d, ((historyWordRows (internalHistory R x ω) w.get).card.choose 2 : ℝ)) := by
      apply expect_mono
      intro ω
      rw [anchoredEdges_card]
      exact internalOffsets_card_le_pairs _
    _ = ∑ w : Word k d, expect (fixedCountPMF cuts) (fun ω =>
        ((historyWordRows (internalHistory R x ω) w.get).card.choose 2 : ℝ)) := expect_sum _ _ _
    _ ≤ ∑ w : Word k d, (R.card.choose 2 : ℝ)*
        (if w.toList.take x.1.val=x.2.toList then RiffleLowerV2.wordMass cuts w^2 else 0) := by
      apply Finset.sum_le_sum
      intro w _
      simp_rw [historyWordRows_internal]
      by_cases hw : w.toList.take x.1.val=x.2.toList
      · simp only [if_pos hw]
        exact restrictedWordBinomialMoment_le cuts R w 2
      · simp only [if_neg hw,Finset.card_empty,Nat.choose_zero_succ,Nat.cast_zero,mul_zero]
        change RiffleLowerV2.expect _ (fun _ => 0) ≤ 0
        rw [expect_const]
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem word_prefixDigits_iff {k d : ℕ} (x : Prefix k d) (w : Word k d) :
    (∀ j : Fin d, w.get j ∈ prefixDigits x j) ↔ w.toList.take x.1.val=x.2.toList := by
  rw [RiffleLowerV2.Thinning.vector_take_eq_iff (Nat.le_of_lt_succ x.1.isLt)]
  constructor
  · intro h j
    simpa [prefixDigits,prefixColumn,Fin.castLE,j.isLt] using h (prefixColumn x j)
  · intro h j
    unfold prefixDigits
    split_ifs with hj
    · simpa [Fin.castLE] using h ⟨j.val,hj⟩
    · exact Finset.mem_univ _

theorem extensionSquareMass_eq {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d) :
    extensionSquareMass cuts x = prefixMass cuts x^2 * tailSquareMass cuts x := by
  let f : Fin d → Fin k → ℝ := fun j a =>
    if a ∈ prefixDigits x j then ((cuts.count j a : ℝ)/n)^2 else 0
  have hw (w : Word k d) :
      (if w.toList.take x.1.val=x.2.toList then RiffleLowerV2.wordMass cuts w^2 else 0) =
        ∏ j : Fin d, f j (w.get j) := by
    by_cases h : ∀ j : Fin d, w.get j ∈ prefixDigits x j
    · rw [if_pos ((word_prefixDigits_iff x w).mp h),GraphOverlap.wordMass_eq_prod,
        ← Finset.prod_pow]
      exact Finset.prod_congr rfl (fun j _ => by simp [f,h j])
    · rw [if_neg (fun hh => h ((word_prefixDigits_iff x w).mpr hh))]
      obtain ⟨j,hj⟩ := not_forall.mp h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [f,hj])).symm
  unfold extensionSquareMass
  simp_rw [hw]
  have hs := (Equiv.vectorEquivFin (Fin k) d).sum_comp (fun w : Fin d → Fin k => ∏ j, f j (w j))
  change (∑ w : Word k d, ∏ j, f j (w.get j)) = _ at hs
  rw [hs,← Fintype.prod_sum f]
  change _ = RiffleLowerV2.prefixMass cuts x^2 * _
  unfold tailSquareMass
  rw [← RiffleLowerV2.Thinning.prefixColumnFraction_product,← Finset.prod_pow,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  change (∑ a : Fin k, f j a) = _ * (if j.val < x.1.val then 1 else _)
  unfold RiffleLowerV2.Thinning.prefixColumnFraction
  by_cases hj : j.val < x.1.val
  · simp [f,prefixDigits,hj]
  · simp [f,prefixDigits,hj]

theorem tailSquareMass_nonneg {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d) :
    0 ≤ tailSquareMass cuts x := by
  unfold tailSquareMass
  apply Finset.prod_nonneg
  intro j _
  split_ifs <;> positivity

/-- Actual restricted two-row collision estimate. The coefficient uses the anchor
size and each future factor uses the original full n-label column population. -/
theorem expected_anchoredEdges_le_collision {k n d : ℕ} (cuts : Cuts k n d)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) :
    expect (fixedCountPMF cuts) (fun ω => ((anchoredEdges c₀ R x ω).card : ℝ)) ≤
      anchoredMean cuts R x^2 * tailSquareMass cuts x / 2 := by
  apply (expected_anchoredEdges_le_collisionMass cuts c₀ R x).trans
  rw [extensionSquareMass_eq,Nat.cast_choose_two]
  unfold anchoredMean
  have hR : (0:ℝ) ≤ R.card := Nat.cast_nonneg _
  have hp : 0 ≤ prefixMass cuts x^2 * tailSquareMass cuts x :=
    mul_nonneg (sq_nonneg _) (tailSquareMass_nonneg cuts x)
  have h := mul_le_mul_of_nonneg_right
    (show (R.card:ℝ)*((R.card:ℝ)-1)/2 ≤ (R.card:ℝ)^2/2 by nlinarith) hp
  convert h using 1 <;> ring

end RiffleUpperV2.Localization
