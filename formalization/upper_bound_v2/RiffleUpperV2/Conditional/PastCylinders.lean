import RiffleUpperV2.Conditional.FutureCylinders

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional

/-- Maximal cylinders contained in the backward interval [s,t). -/
def pastCylinders {k K : ℕ} (s t : Word k K) : Finset (Prefix k K) :=
  Finset.univ.filter fun x =>
    (∃ w : Word k K, inCylinder x w) ∧
    (∀ w : Word k K, inCylinder x w → s ≤ w ∧ w < t) ∧
    (∃ w : Word k K, parentList x <+: w.toList ∧ ¬ (s ≤ w ∧ w < t))

/-- Every word of the backward interval has a shortest fully contained prefix. -/
theorem pastCylinders_cover {k K : ℕ} (s t w : Word k K) :
    s ≤ w ∧ w < t ↔ ∃ x ∈ pastCylinders s t, inCylinder x w := by
  constructor
  · intro hw
    let P : ℕ → Prop := fun d => ∀ v : Word k K,
      w.toList.take d <+: v.toList → s ≤ v ∧ v < t
    have hPK : P K := by
      intro v hv
      have he : w = v := by
        apply Subtype.ext
        apply List.IsPrefix.eq_of_length _ (by simp)
        simpa only [← List.Vector.toList_length w, List.take_length, List.Vector.toList] using hv
      simpa only [← he] using hw
    have hex : ∃ d, P d := ⟨K,hPK⟩
    let d := Nat.find hex
    have hdK : d ≤ K := Nat.find_min' hex hPK
    have hPd : P d := Nat.find_spec hex
    have hd0 : 0 < d := by
      by_contra h
      have hd : d = 0 := by omega
      have hh := hPd t (by simp [hd])
      exact (lt_irrefl t) hh.2
    have hn : ¬ P (d-1) := Nat.find_min hex (by omega)
    obtain ⟨v,hv'⟩ := not_forall.mp hn
    obtain ⟨hv,hout⟩ := Classical.not_imp.mp hv'
    let x := wordPrefix w d hdK
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · refine ⟨⟨w, List.take_prefix _ _⟩, hPd, v, ?_, hout⟩
      simpa only [parentList, x, wordPrefix, RiffleShuffle.truncate,
        List.Vector.toList, List.take_take, Nat.min_eq_left (Nat.sub_le d 1)] using hv
    · exact List.take_prefix _ _
  · rintro ⟨x,hx,hw⟩
    exact (Finset.mem_filter.mp hx).2.2.1 w hw

/-- A maximal contained cylinder is never the root: the current right endpoint is excluded. -/
theorem pastCylinders_depth_pos {k K : ℕ} (s t : Word k K)
    {x : Prefix k K} (hx : x ∈ pastCylinders s t) : 0 < x.1.val := by
  obtain ⟨hw,hin,v,hv,hout⟩ := (Finset.mem_filter.mp hx).2
  by_contra h
  have hd : x.1.val = 0 := by omega
  have he : x.2.toList = [] := List.eq_nil_of_length_eq_zero (by simpa only [List.Vector.toList_length] using hd)
  exact hout (hin v (by simp [inCylinder,he]))

/-- Distinct maximal cylinders are disjoint, including on zero-mass words. -/
theorem pastCylinders_disjoint {k K : ℕ} (s t : Word k K)
    {x y : Prefix k K} (hx : x ∈ pastCylinders s t) (hy : y ∈ pastCylinders s t)
    {w : Word k K} (hxw : inCylinder x w) (hyw : inCylinder y w) : x = y := by
  have hcmp := List.prefix_or_prefix_of_prefix hxw hyw
  have hno {a b : Prefix k K} (ha : a ∈ pastCylinders s t)
      (hb : b ∈ pastCylinders s t) (hab : a.2.toList <+: b.2.toList) : a = b := by
    by_cases he : a.1.val = b.1.val
    · exact prefix_ext (hab.eq_of_length (by simpa only [List.Vector.toList_length] using he))
    · have hl : a.1.val < b.1.val := by
        have hh := hab.length_le
        simp only [List.Vector.toList_length] at hh
        omega
      have hp : a.2.toList <+: parentList b := by
        apply List.prefix_take_iff.mpr
        exact ⟨hab, by simpa only [List.Vector.toList_length] using (show a.1.val ≤ b.1.val-1 by omega)⟩
      obtain ⟨v,hv,hout⟩ := (Finset.mem_filter.mp hb).2.2.2
      exact False.elim (hout ((Finset.mem_filter.mp ha).2.2.1 v (hp.trans hv)))
  rcases hcmp with h | h
  · exact hno hx hy h
  · exact (hno hy hx h).symm

/-- Every parent of a selected cylinder meets one of the two endpoint branches. -/
theorem pastCylinders_parent_endpoint {k K : ℕ} (s t : Word k K)
    {x : Prefix k K} (hx : x ∈ pastCylinders s t) :
    parentList x <+: s.toList ∨ parentList x <+: t.toList := by
  obtain ⟨⟨w,hw⟩,hin,v,hv,hout⟩ := (Finset.mem_filter.mp hx).2
  have hsw := (hin w hw).1
  have hwt := (hin w hw).2
  have hpw : parentList x <+: w.toList := (List.take_prefix _ _).trans hw
  by_cases hvs : v < s
  · exact Or.inl (RiffleShuffle.prefix_lex_convex hvs.le hsw hv hpw)
  · have htv : t ≤ v := by
      have hsv : s ≤ v := le_of_not_gt hvs
      exact le_of_not_gt (fun h => hout ⟨hsv,h⟩)
    exact Or.inr (RiffleShuffle.prefix_lex_convex hwt.le htv hpw hv)

/-- Structural antichain form required by the actual future-cylinder law. -/
theorem pastCylinders_antichain {k K : ℕ} (s t : Word k K)
    {x y : Prefix k K} (hx : x ∈ pastCylinders s t) (hy : y ∈ pastCylinders s t)
    (hne : x ≠ y) :
    ¬ (x.2.toList <+: y.2.toList) ∧ ¬ (y.2.toList <+: x.2.toList) := by
  constructor
  · intro hxy
    obtain ⟨w,hyw⟩ := (Finset.mem_filter.mp hy).2.1
    exact hne (pastCylinders_disjoint s t hx hy (hxy.trans hyw) hyw)
  · intro hyx
    obtain ⟨w,hxw⟩ := (Finset.mem_filter.mp hx).2.1
    exact hne (pastCylinders_disjoint s t hx hy hxw (hyx.trans hxw))

theorem pastCylinders_child {k K : ℕ} (s t : Word k K)
    {x : Prefix k K} (hx : x ∈ pastCylinders s t) :
    ∃ j : Fin K, ∃ a : Fin k, x = endpointChild s j a ∨ x = endpointChild t j a := by
  have hd := pastCylinders_depth_pos s t hx
  let j : Fin K := ⟨x.1.val-1, by have := x.1.isLt; omega⟩
  have hne : x.2.toList ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.Vector.toList_length, List.length_nil] at hlen
    omega
  let a := x.2.toList.getLast hne
  have hp : parentList x ++ [a] = x.2.toList := by
    simpa only [parentList, ← List.Vector.toList_length x.2, ← List.dropLast_eq_take, a]
      using List.dropLast_append_getLast hne
  have hlen : (parentList x).length = j.val := by
    simp [parentList,j]
  have hc (w : Word k K) (hw : parentList x <+: w.toList) : x = endpointChild w j a := by
    apply prefix_ext
    have he := List.prefix_iff_eq_take.mp hw
    rw [hlen] at he
    change x.2.toList = w.toList.take j.val ++ [a]
    rw [← hp, he]
  refine ⟨j,a,?_⟩
  rcases pastCylinders_parent_endpoint s t hx with hs | ht
  · exact Or.inl (hc s hs)
  · exact Or.inr (hc t ht)

/-- The endpoint branches contain at most 2kK maximal cylinders, even when
some digits have zero mass and occupied cylinders are empty. -/
theorem pastCylinders_card {k K : ℕ} (s t : Word k K) :
    (pastCylinders s t).card ≤ 2*k*K := by
  let f : Bool × Fin K × Fin k → Prefix k K :=
    fun v => endpointChild (if v.1 then s else t) v.2.1 v.2.2
  have hsub : pastCylinders s t ⊆ Finset.univ.image f := by
    intro x hx
    obtain ⟨j,a,h | h⟩ := pastCylinders_child s t hx
    · exact Finset.mem_image.mpr ⟨(true,j,a),Finset.mem_univ _,by simpa [f] using h.symm⟩
    · exact Finset.mem_image.mpr ⟨(false,j,a),Finset.mem_univ _,by simpa [f] using h.symm⟩
  calc
    _ ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ Fintype.card (Bool × Fin K × Fin k) := Finset.card_image_le.trans_eq (Finset.card_univ)
    _ = _ := by simp [Fintype.card_prod]; ring

/-- Source backward interval decomposition with its disjointness and
finite count stated together. -/
theorem pastCylinderDecomposition {k K : ℕ} (s t : Word k K) :
    (pastCylinders s t).card ≤ 2*k*K ∧
    (∀ w : Word k K, (s ≤ w ∧ w < t) ↔
      ∃ x ∈ pastCylinders s t, inCylinder x w) ∧
    (∀ x ∈ pastCylinders s t, ∀ y ∈ pastCylinders s t, x ≠ y →
      ¬ (x.2.toList <+: y.2.toList) ∧ ¬ (y.2.toList <+: x.2.toList)) :=
  ⟨pastCylinders_card s t, pastCylinders_cover s t,
    fun _ hx _ hy hne => pastCylinders_antichain s t hx hy hne⟩

end RiffleUpperV2.Conditional
