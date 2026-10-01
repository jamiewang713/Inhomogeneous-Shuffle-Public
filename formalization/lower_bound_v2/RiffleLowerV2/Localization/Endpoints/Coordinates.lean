import RiffleLowerV2.Localization.Endpoints.Partitions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Localization
open TimeProfile

theorem take_eq_take_iff {k K l : ℕ} (hl : l ≤ K) (v a : Word k K) :
    v.toList.take l = a.toList.take l ↔
      ∀ j : Fin K, j.val < l → v.get j = a.get j := by
  constructor
  · intro h j hj
    have hjv : j.val < (v.toList.take l).length := by simp [Nat.min_eq_left hl, hj]
    have hja : j.val < (a.toList.take l).length := by simp [Nat.min_eq_left hl, hj]
    have he := (List.ext_getElem_iff.mp h).2 j.val hjv hja
    simpa [List.Vector.get, List.get_eq_getElem, List.Vector.toList] using he
  · intro h
    apply List.ext_getElem (by simp)
    intro j hj hj'
    have hjl : j < l := by simpa [Nat.min_eq_left hl] using hj
    have he := h ⟨j, lt_of_lt_of_le hjl hl⟩ hjl
    simpa [List.Vector.get, List.get_eq_getElem, List.Vector.toList] using he

theorem sidePrefix_coordinates {k K l m : ℕ} (a v : Word k K)
    (hlm : l ≤ m) (hm : m ≤ K) (x : WordOn k (columnSet K l m))
    (j : columnSet K l m) (d : Fin k) :
    v.toList.take (sidePrefix a l m x j d).1.val = (sidePrefix a l m x j d).2.toList ↔
      v.toList.take l = a.toList.take l ∧ sideMatch x (restrictWord (columnSet K l m) v) j d := by
  have hjl : l ≤ j.val.val := (Finset.mem_filter.mp j.property).2.1
  have hjm : j.val.val < m := (Finset.mem_filter.mp j.property).2.2
  have hjK : j.val.val+1 ≤ K := by omega
  let w : Word k K := List.Vector.ofFn fun h : Fin K =>
    if h = j.val then d else if hh : h ∈ columnSet K l m then x ⟨h, hh⟩ else a.get h
  change v.toList.take (min (j.val.val+1) K) = (prefixAt (j.val.val+1) w).2.toList ↔ _
  rw [Nat.min_eq_left hjK, prefixAt_toList _ _ hjK, take_eq_take_iff hjK,
    take_eq_take_iff (hlm.trans hm)]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro q hql
      have hqj : q ≠ j.val := by intro he; have := congrArg Fin.val he; omega
      have hqI : q ∉ columnSet K l m := by simp [columnSet]; omega
      simpa [w, hqj, hqI] using h q (by omega)
    · simpa [w, restrictWord] using h j.val (by omega)
    · intro q hqj
      have hqj' : q.val ≠ j.val := fun he => (ne_of_lt hqj) (Subtype.ext he)
      have hqjval : q.val.val < j.val.val := hqj
      simpa [w, restrictWord, hqj', q.property] using h q.val (by omega)
  · rintro ⟨ha, hj, hpre⟩ q hq
    by_cases hqj : q = j.val
    · subst q
      simpa [w, restrictWord] using hj
    · by_cases hqI : q ∈ columnSet K l m
      · have hlt : (⟨q, hqI⟩ : columnSet K l m) < j := by
          change q.val < j.val.val
          have hne : q.val ≠ j.val.val := fun he => hqj (Fin.ext he)
          omega
        simpa [w, restrictWord, hqj, hqI] using hpre ⟨q, hqI⟩ hlt
      · have hql : q.val < l := by
          have hnot : ¬(l ≤ q.val ∧ q.val < m) := by simpa [columnSet] using hqI
          omega
        simpa [w, hqj, hqI] using ha q hql

end RiffleLowerV2.Localization
