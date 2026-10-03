import RiffleUpperV2.Anchor.UnequalDefinitions

noncomputable section
namespace RiffleUpperV2.Anchor
open TimeProfile

theorem rowSlice_matches {k n d : ℕ} {cuts : Cuts k n d} (ω : Sample cuts)
    (r : Fin n) (x : Prefix k d) (lo hi : ℕ) (hlh : lo ≤ hi) (hhi : hi ≤ x.1.val)
    (h : ∀ t : Fin x.1.val, lo ≤ t.val → t.val < hi →
      sampleEntry ω r (prefixColumn x t) = x.2.get t) :
    rowSlice ω r lo hi = (x.2.toList.take hi).drop lo := by
  have hhid : hi ≤ d := hhi.trans (Nat.le_of_lt_succ x.1.isLt)
  apply List.ext_getElem
  · simp only [rowSlice, List.length_drop, List.length_take, List.Vector.toList_length,
      Nat.min_eq_left hhi, Nat.min_eq_left hhid]
  · intro i hi₁ hi₂
    have hit : lo+i < hi := by
      simp only [rowSlice, List.length_drop, List.length_take, List.Vector.toList_length,
        Nat.min_eq_left hhid] at hi₁
      omega
    let t : Fin x.1.val := ⟨lo+i, lt_of_lt_of_le hit hhi⟩
    have he := (RiffleLowerV2.rowWord_get ω r (prefixColumn x t)).trans
      (h t (by change lo ≤ lo+i; omega) hit)
    simpa only [rowSlice, List.getElem_drop, List.getElem_take,
      List.Vector.get, List.Vector.toList, Fin.cast, List.get_eq_getElem, t, prefixColumn] using he

/-- A strict first difference after lo decides the entire suffix through x.
No digit later than the strict witness is inspected or restricted. -/
theorem rowSuffix_side_of_first_difference {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (ω : Sample cuts) (r : Fin n) (x : Prefix k d)
    (lo : ℕ) (i : Fin x.1.val) (hlo : lo ≤ i.val)
    (he : ∀ t : Fin x.1.val, lo ≤ t.val → t.val < i.val →
      sampleEntry ω r (prefixColumn x t) = x.2.get t)
    (hi : s.test (sampleEntry ω r (prefixColumn x i)) (x.2.get i)) :
    s.test (rowSlice ω r lo x.1.val) (x.2.toList.drop lo) := by
  let u := rowSlice ω r lo x.1.val
  let v := x.2.toList.drop lo
  let t := i.val-lo
  have htx : t < x.1.val-lo := by dsimp [t]; omega
  have htu : t < u.length := by
    dsimp [u, rowSlice]
    simp only [List.length_drop, List.length_take, List.Vector.toList_length,
      Nat.min_eq_left (Nat.le_of_lt_succ x.1.isLt)]
    exact htx
  have htv : t < v.length := by simpa only [v, List.length_drop, List.Vector.toList_length] using htx
  have htake : u.take t = v.take t := by
    have h := rowSlice_matches ω r x lo i.val hlo i.isLt.le he
    simpa only [u, v, t, rowSlice, List.take_drop, List.take_take,
      Nat.add_sub_of_le hlo, Nat.min_eq_left i.isLt.le] using h
  have hu : u[t] = sampleEntry ω r (prefixColumn x i) := by
    have hh := RiffleLowerV2.rowWord_get ω r (prefixColumn x i)
    simpa only [u, t, rowSlice, List.getElem_drop, List.getElem_take,
      Nat.add_sub_of_le hlo, List.Vector.get, List.Vector.toList, Fin.cast,
      List.get_eq_getElem, prefixColumn] using hh
  have hv : v[t] = x.2.get i := by
    simp only [v, t, List.getElem_drop, Nat.add_sub_of_le hlo,
      List.Vector.get, List.Vector.toList, Fin.cast, List.get_eq_getElem]
  cases s
  · apply (list_split_lt_iff u v t htu htv).mpr
    exact Or.inr ⟨htake, Or.inl (by rw [hu,hv]; exact hi)⟩
  · apply (list_split_lt_iff v u t htv htu).mpr
    exact Or.inr ⟨htake.symm, Or.inl (by rw [hu,hv]; exact hi)⟩

end RiffleUpperV2.Anchor
