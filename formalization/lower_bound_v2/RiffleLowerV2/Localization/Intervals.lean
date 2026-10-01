import RiffleLowerV2.Shared.Geometry
import Mathlib.Data.Int.Interval

noncomputable section
open scoped BigOperators
namespace RiffleLowerV2.Localization
attribute [local instance] Classical.propDecidable

@[simp] theorem mem_integerHalfOpen (l r : ℝ) (z : ℤ) :
    z ∈ integerHalfOpen l r ↔ l ≤ (z : ℝ) ∧ (z : ℝ) < r := by
  constructor
  · intro hz
    exact (Finset.mem_filter.mp hz).2
  · intro hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hz⟩
    · exact_mod_cast (Int.floor_le l).trans hz.1
    · exact_mod_cast hz.2.le.trans (Int.le_ceil r)

theorem integerHalfOpen_eq_Ico (l r : ℝ) :
    integerHalfOpen l r = Finset.Ico ⌈l⌉ ⌈r⌉ := by
  ext z
  simp only [mem_integerHalfOpen, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]

theorem integerHalfOpen_card_eq {l r : ℝ} (hlr : l ≤ r) :
    ((integerHalfOpen l r).card : ℝ) = (⌈r⌉ : ℝ) - (⌈l⌉ : ℝ) := by
  rw [integerHalfOpen_eq_Ico]
  exact_mod_cast Int.card_Ico_of_le ⌈l⌉ ⌈r⌉ (Int.ceil_mono hlr)

theorem integerHalfOpen_card_bounds {l r : ℝ} (hlr : l ≤ r) :
    r-l-1 ≤ ((integerHalfOpen l r).card : ℝ) ∧
    ((integerHalfOpen l r).card : ℝ) ≤ r-l+1 := by
  rw [integerHalfOpen_card_eq hlr]
  constructor <;> linarith [Int.le_ceil l, Int.le_ceil r,
    Int.ceil_lt_add_one l, Int.ceil_lt_add_one r]

theorem integerHalfOpen_disjoint {l r l' r' : ℝ} (h : r ≤ l') :
    Disjoint (integerHalfOpen l r) (integerHalfOpen l' r') := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hz := (mem_integerHalfOpen _ _ _).mp hz
  have hz' := (mem_integerHalfOpen _ _ _).mp hz'
  linarith

@[simp] theorem mem_integerBoundary (H : Finset ℤ) (z : ℤ) :
    z ∈ integerBoundary H ↔ (z ∈ H ∧ z+1 ∉ H) ∨ (z ∉ H ∧ z+1 ∈ H) := by
  constructor
  · exact fun hz => (Finset.mem_filter.mp hz).2
  · intro hz
    apply Finset.mem_filter.mpr
    refine ⟨?_, hz⟩
    rcases hz with hz | hz
    · exact Finset.mem_union_left _ hz.1
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨z+1, hz.2, by omega⟩

theorem integerBoundary_union_subset (H J : Finset ℤ) :
    integerBoundary (H ∪ J) ⊆ integerBoundary H ∪ integerBoundary J := by
  intro z hz
  simp only [mem_integerBoundary, Finset.mem_union] at hz ⊢
  tauto

theorem integerBoundary_inter_subset (H J : Finset ℤ) :
    integerBoundary (H ∩ J) ⊆ integerBoundary H ∪ integerBoundary J := by
  intro z hz
  simp only [mem_integerBoundary, Finset.mem_union, Finset.mem_inter] at hz ⊢
  tauto

theorem integerBoundary_biUnion_subset {α : Type*} (S : Finset α) (H : α → Finset ℤ) :
    integerBoundary (S.biUnion H) ⊆ S.biUnion (fun a => integerBoundary (H a)) := by
  intro z hz
  rw [mem_integerBoundary] at hz
  rcases hz with ⟨hz, hn⟩ | ⟨hn, hz⟩
  · obtain ⟨a, ha, hz⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨a, ha, (mem_integerBoundary _ _).mpr
      (Or.inl ⟨hz, fun h => hn (Finset.mem_biUnion.mpr ⟨a, ha, h⟩)⟩)⟩
  · obtain ⟨a, ha, hz⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨a, ha, (mem_integerBoundary _ _).mpr
      (Or.inr ⟨fun h => hn (Finset.mem_biUnion.mpr ⟨a, ha, h⟩), hz⟩)⟩

theorem integerBoundary_Ico_subset (a b : ℤ) :
    integerBoundary (Finset.Ico a b) ⊆ {a-1,b-1} := by
  intro z hz
  simp only [mem_integerBoundary, Finset.mem_Ico] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem integerBoundary_Ico_card_le (a b : ℤ) :
    (integerBoundary (Finset.Ico a b)).card ≤ 2 := by
  exact (Finset.card_le_card (integerBoundary_Ico_subset a b)).trans
    ((Finset.card_insert_le _ _).trans (by simp))

theorem integerBoundary_integerHalfOpen_card_le (l r : ℝ) :
    (integerBoundary (integerHalfOpen l r)).card ≤ 2 := by
  rw [integerHalfOpen_eq_Ico]
  exact integerBoundary_Ico_card_le _ _

theorem integerBoundary_intervalUnion_card_le {α : Type*} (S : Finset α)
    (l r : α → ℝ) :
    (integerBoundary (S.biUnion fun a => integerHalfOpen (l a) (r a))).card ≤ 2*S.card := by
  calc
    _ ≤ (S.biUnion fun a => integerBoundary (integerHalfOpen (l a) (r a))).card :=
      Finset.card_le_card (integerBoundary_biUnion_subset _ _)
    _ ≤ ∑ a ∈ S, (integerBoundary (integerHalfOpen (l a) (r a))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S, 2 := Finset.sum_le_sum fun a _ =>
      integerBoundary_integerHalfOpen_card_le (l a) (r a)
    _ = _ := by simp [Nat.mul_comm]

theorem integerBoundary_translate (H : Finset ℤ) (q : ℤ) :
    integerBoundary (H.image (fun z => z+q)) =
      (integerBoundary H).image (fun z => z+q) := by
  have hm (z : ℤ) : z ∈ H.image (fun z => z+q) ↔ z-q ∈ H := by
    constructor
    · rintro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      simpa using ha
    · intro hz
      exact Finset.mem_image.mpr ⟨z-q, hz, by omega⟩
  ext z
  rw [mem_integerBoundary, hm, hm]
  constructor
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨z-q, (mem_integerBoundary _ _).mpr ?_, by omega⟩
    simpa only [show z+1-q = z-q+1 by omega] using h
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    simpa only [add_sub_cancel_right, show a+q+1-q = a+1 by omega] using
      (mem_integerBoundary _ _).mp ha

theorem rankSet_clipTranslate (N : ℕ) (H : Finset ℤ) (q : ℤ) :
    rankSet (clipTranslate N H q) =
      (H.image (fun z => z+q)) ∩ Finset.Ico 1 ((N : ℤ)+1) := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨manuscriptRank i-q,
        (mem_clipTranslate _ _ _).mp hi, by omega⟩
    · simp only [Finset.mem_Ico, manuscriptRank]
      omega
  · intro hz
    obtain ⟨hi, hdeck⟩ := Finset.mem_inter.mp hz
    obtain ⟨a, ha, hza⟩ := Finset.mem_image.mp hi
    have hz1 := (Finset.mem_Ico.mp hdeck).1
    have hzN := (Finset.mem_Ico.mp hdeck).2
    let i : Fin N := ⟨(z-1).toNat, by omega⟩
    have hrank : manuscriptRank i = z := by dsimp [manuscriptRank, i]; omega
    apply Finset.mem_image.mpr
    refine ⟨i, (mem_clipTranslate _ _ _).mpr ?_, hrank⟩
    rw [hrank, ← hza]
    simpa using ha

theorem boundary_clipTranslate_le (N : ℕ) (H : Finset ℤ) (q : ℤ) :
    (boundary (clipTranslate N H q)).card ≤ (integerBoundary H).card + 2 := by
  unfold boundary
  rw [rankSet_clipTranslate]
  calc
    _ ≤ (integerBoundary (H.image (fun z => z+q)) ∪
        integerBoundary (Finset.Ico 1 ((N : ℤ)+1))).card :=
      Finset.card_le_card (integerBoundary_inter_subset _ _)
    _ ≤ (integerBoundary (H.image (fun z => z+q))).card +
        (integerBoundary (Finset.Ico 1 ((N : ℤ)+1))).card := Finset.card_union_le _ _
    _ ≤ (integerBoundary H).card + 2 := by
      rw [integerBoundary_translate, Finset.card_image_of_injective _
        (show Function.Injective (fun z : ℤ => z+q) by intro a b h; exact add_right_cancel h)]
      exact Nat.add_le_add_left (integerBoundary_Ico_card_le _ _) _

theorem intervalUnion_card_bounds {α : Type*} (S : Finset α) (l r : α → ℝ)
    (hlr : ∀ a ∈ S, l a ≤ r a)
    (hd : (S : Set α).PairwiseDisjoint fun a => integerHalfOpen (l a) (r a)) :
    (∑ a ∈ S, (r a-l a)) - S.card ≤
      ((S.biUnion fun a => integerHalfOpen (l a) (r a)).card : ℝ) ∧
    ((S.biUnion fun a => integerHalfOpen (l a) (r a)).card : ℝ) ≤
      (∑ a ∈ S, (r a-l a)) + S.card := by
  rw [Finset.card_biUnion hd, Nat.cast_sum]
  constructor
  · calc
      _ = ∑ a ∈ S, (r a-l a-1) := by simp [Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum fun a ha => (integerHalfOpen_card_bounds (hlr a ha)).1
  · calc
      _ ≤ ∑ a ∈ S, (r a-l a+1) := Finset.sum_le_sum fun a ha =>
        (integerHalfOpen_card_bounds (hlr a ha)).2
      _ = _ := by simp [Finset.sum_add_distrib]

end RiffleLowerV2.Localization
