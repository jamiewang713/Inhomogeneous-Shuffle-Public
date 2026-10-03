import RiffleUpperV2.Anchor.Main
import RiffleUpperV2.Localization.RankGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor Hypergeometric TimeProfile

/-- The actual first-difference sibling cylinder at a future digit. -/
def sideRows {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val) (ω : Sample cuts) :=
  cylinderSet cuts R (prefixThenDigits x i (s.strictDigits (x.2.get i))) ω

theorem sideRows_mem {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val) (ω : Sample cuts) (r : Fin n) :
    r ∈ sideRows cuts s R x i ω ↔ r ∈ R ∧
      (rowWord ω r).toList.take i.val = x.2.toList.take i.val ∧
      s.test (sampleEntry ω r (prefixColumn x i)) (x.2.get i) := by
  unfold sideRows prefixThenDigits
  rw [cylinderSet_update_univ cuts R _ _ _ (prefixBefore_univ x i),
    ← prefixRows_eq_cylinderSet]
  simp only [Finset.mem_filter, Anchor.prefixRows, takePrefix, RiffleShuffle.truncate, List.Vector.toList,
    SuffixSide.strictDigits, Finset.mem_univ, true_and]
  tauto

theorem sideRows_expect {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val) :
    expect (fixedCountPMF cuts) (fun ω => ((sideRows cuts s R x i ω).card : ℝ)) =
      sideMean s cuts R x i := by
  exact (cylinderMean_eq_expect cuts R _).symm.trans (sideMean_eq_cylinderMean cuts hn s R x i)

theorem sideRows_tail {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i : Fin x.1.val)
    {t : ℝ} (ht : 0 < t) :
    probability (fixedCountPMF cuts)
      (fun ω => t ≤ |((sideRows cuts s R x i ω).card : ℝ) - sideMean s cuts R x i|) ≤
      2*Real.exp (-t^2/(4*(sideMean s cuts R x i+t))) := by
  have h := (anchorCylinderTail cuts R (prefixThenDigits x i (s.strictDigits (x.2.get i))) ht).1
  simpa only [sideMean_eq_cylinderMean cuts hn, sideRows, cylinderCount] using h

private theorem list_lt_first_difference {α : Type*} [LinearOrder α]
    (u v : List α) (hlen : u.length = v.length) :
    u < v ↔ ∃ i : ℕ, ∃ hi : i < u.length, ∃ hj : i < v.length,
      u.take i = v.take i ∧ u[i] < v[i] := by
  induction u generalizing v with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
    subst v
    simp
  | cons a u ih =>
    cases v with
    | nil => simp at hlen
    | cons b v =>
      have hl : u.length = v.length := by simpa using hlen
      constructor
      · intro h
        rcases (list_cons_lt_iff a b u v).mp h with hab | ⟨hab,huv⟩
        · exact ⟨0,by simp,by simp,by simp,by simpa using hab⟩
        · obtain ⟨i,hi,hj,htake,hd⟩ := (ih v hl).mp huv
          refine ⟨i+1,by simpa using hi,by simpa using hj,?_,?_⟩
          · simp [hab,htake]
          · simpa using hd
      · rintro ⟨i,hi,hj,htake,hd⟩
        exact (list_split_lt_iff (a::u) (b::v) i hi hj).mpr
          (Or.inr ⟨htake,Or.inl hd⟩)

theorem row_side_iff_exists_piece {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) (r : Fin n) :
    r ∈ R ∧ s.test ((rowWord ω r).toList.take x.1.val) x.2.toList ↔
      ∃ i : Fin x.1.val, r ∈ sideRows cuts s R x i ω := by
  have hlen : ((rowWord ω r).toList.take x.1.val).length = x.2.toList.length := by
    simp only [List.length_take,List.Vector.toList_length,
      Nat.min_eq_left (Nat.le_of_lt_succ x.1.isLt)]
  have convert_witness (i : Fin x.1.val) :
      ((rowWord ω r).toList.take x.1.val).take i.val = x.2.toList.take i.val ↔
      (rowWord ω r).toList.take i.val = x.2.toList.take i.val := by
    simp [List.take_take, Nat.min_eq_left i.isLt.le]
  cases s with
  | lower =>
    change r ∈ R ∧ _ < _ ↔ _
    rw [list_lt_first_difference _ _ hlen]
    constructor
    · rintro ⟨hr,i,hi,hj,he,hd⟩
      have hi' : i < x.1.val := by simpa using hj
      let t : Fin x.1.val := ⟨i,hi'⟩
      refine ⟨t,(sideRows_mem cuts .lower R x t ω r).mpr ⟨hr,?_,?_⟩⟩
      · exact (convert_witness t).mp he
      · have hg := rowSlice_get ω r x t
        simpa only [SuffixSide.test, List.Vector.get, List.Vector.toList,
          Fin.cast, List.get_eq_getElem] using hg.symm ▸ hd
    · rintro ⟨i,hi⟩
      obtain ⟨hr,he,hd⟩ := (sideRows_mem cuts .lower R x i ω r).mp hi
      refine ⟨hr,i.val,by rw [hlen]; simpa using i.isLt,by simpa using i.isLt,
        (convert_witness i).mpr he,?_⟩
      rw [rowSlice_get]
      exact hd
  | upper =>
    change r ∈ R ∧ _ < _ ↔ _
    rw [list_lt_first_difference _ _ hlen.symm]
    constructor
    · rintro ⟨hr,i,hi,hj,he,hd⟩
      have hi' : i < x.1.val := by simpa using hi
      let t : Fin x.1.val := ⟨i,hi'⟩
      refine ⟨t,(sideRows_mem cuts .upper R x t ω r).mpr ⟨hr,?_,?_⟩⟩
      · exact (convert_witness t).mp he.symm
      · have hg := rowSlice_get ω r x t
        simpa only [SuffixSide.test, List.Vector.get, List.Vector.toList,
          Fin.cast, List.get_eq_getElem] using hg.symm ▸ hd
    · rintro ⟨i,hi⟩
      obtain ⟨hr,he,hd⟩ := (sideRows_mem cuts .upper R x i ω r).mp hi
      refine ⟨hr,i.val,by simpa using i.isLt,by rw [hlen]; simpa using i.isLt,
        ((convert_witness i).mpr he).symm,?_⟩
      rw [rowSlice_get]
      exact hd


theorem sideRows_before {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) {i j : Fin x.1.val} (hij : i.val < j.val)
    (ω : Sample cuts) {r : Fin n} (hr : r ∈ sideRows cuts s R x j ω) :
    sampleEntry ω r (prefixColumn x i) = x.2.get i := by
  simp only [sideRows, cylinderSet, RiffleLowerV2.Thinning.intersectionWithin,
    Finset.mem_filter, Finset.mem_univ, true_and] at hr
  have hh := hr.2 (prefixColumn x i)
  rw [prefixThenDigits_before x j i _ hij] at hh
  exact Finset.mem_singleton.mp hh

theorem sideRows_disjoint {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) {i j : Fin x.1.val} (hne : i ≠ j)
    (ω : Sample cuts) : Disjoint (sideRows cuts s R x i ω) (sideRows cuts s R x j ω) := by
  have aux {i j : Fin x.1.val} (hij : i.val < j.val) :
      Disjoint (sideRows cuts s R x i ω) (sideRows cuts s R x j ω) := by
    apply Finset.disjoint_left.mpr
    intro r hi hj
    have he := sideRows_before cuts s R x hij ω hj
    have ht := ((sideRows_mem cuts s R x i ω r).mp hi).2.2
    rw [he] at ht
    cases s <;> exact lt_irrefl _ ht
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hne (Fin.ext h)) with h | h
  · exact aux h
  · exact (aux h).symm

theorem side_count_eq_sum {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    (R.filter (fun r => s.test ((rowWord ω r).toList.take x.1.val) x.2.toList)).card =
      ∑ i : Fin x.1.val, (sideRows cuts s R x i ω).card := by
  have he : R.filter (fun r => s.test ((rowWord ω r).toList.take x.1.val) x.2.toList) =
      Finset.univ.biUnion (fun i : Fin x.1.val => sideRows cuts s R x i ω) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact row_side_iff_exists_piece cuts s R x ω r
  rw [he, Finset.card_biUnion]
  intro i _ j _ hne
  exact sideRows_disjoint cuts s R x hne ω

theorem lowerEndpoint_side_sum {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    lowerEndpoint c₀ R x ω = c₀ + ∑ i : Fin x.1.val, ((sideRows cuts .lower R x i ω).card : ℤ) := by
  unfold lowerEndpoint
  have h := side_count_eq_sum cuts .lower R x ω
  simp only [SuffixSide.test] at h
  rw [h, Nat.cast_sum]

theorem upperEndpoint_side_sum {k n d : ℕ} (cuts : Cuts k n d) (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    upperEndpoint c₀ R x ω = c₀ + R.card -
      ∑ i : Fin x.1.val, ((sideRows cuts .upper R x i ω).card : ℤ) := by
  rw [upperEndpoint_eq_le_count]
  have h := side_count_eq_sum cuts .upper R x ω
  simp only [SuffixSide.test] at h
  have hc := Finset.card_filter_add_card_filter_not
    (s := R) (p := fun r => (rowWord ω r).toList.take x.1.val ≤ x.2.toList)
  simp only [not_le] at hc
  rw [h] at hc
  have hc' : ((R.filter (fun r => (rowWord ω r).toList.take x.1.val ≤ x.2.toList)).card : ℤ) +
      ∑ i : Fin x.1.val, ((sideRows cuts .upper R x i ω).card : ℤ) = R.card := by
    exact_mod_cast hc
  omega

end RiffleUpperV2.Localization
