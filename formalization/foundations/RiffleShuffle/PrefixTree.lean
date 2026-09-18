import RiffleShuffle.Words

/-! Legal prefix trees and cylinder lemmas T01–T15 from the frozen contract. -/

noncomputable section
namespace RiffleShuffle

variable {N k K : ℕ} {P : PileProfile N k K}

def root (P : PileProfile N k K) : Node P :=
  ⟨⟨⟨0, Nat.zero_lt_succ K⟩, emptyWord k⟩, legal_empty P⟩

def parent (x : Node P) : Node P :=
  ⟨⟨⟨x.depth - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.1.1.isLt⟩,
      truncate (Nat.sub_le x.depth 1) x.word⟩,
    legal_truncate x.2 (Nat.sub_le x.depth 1)⟩

/-- T01. -/
theorem node_prefix_refl (x : Node P) : x.IsPrefix x := List.prefix_refl _

/-- T02. -/
theorem node_prefix_trans {x y z : Node P}
    (hxy : x.IsPrefix y) (hyz : y.IsPrefix z) : x.IsPrefix z := hxy.trans hyz

/-- T03. -/
theorem node_prefix_antisymm {x y : Node P}
    (hxy : x.IsPrefix y) (hyx : y.IsPrefix x) : x = y := by
  rcases x with ⟨⟨mx, x⟩, hx⟩
  rcases y with ⟨⟨my, y⟩, hy⟩
  change x.toList <+: y.toList at hxy
  change y.toList <+: x.toList at hyx
  have hlist : x.toList = y.toList := hxy.eq_of_length_le hyx.length_le
  have hdepth : mx = my := Fin.ext (x.2.symm.trans ((congrArg List.length hlist).trans y.2))
  subst my
  have hword : x = y := Subtype.ext hlist
  subst y
  rfl

/-- T04. -/
theorem root_prefix (x : Node P) : (root P).IsPrefix x := List.nil_prefix

/-- T05. -/
theorem parent_prefix (x : Node P) : (parent x).IsPrefix x :=
  truncate_prefix (Nat.sub_le x.depth 1) x.word

/-- T06. -/
theorem parent_depth (x : Node P) : (parent x).depth = x.depth - 1 := rfl

/-- T07. -/
theorem parent_strict (x : Node P) (h : 0 < x.depth) : (parent x).depth < x.depth := by
  rw [parent_depth]
  omega

/-- T08. -/
theorem exists_child (x : Node P) (h : x.depth < K) : ∃ y : Node P, Child x y := by
  obtain ⟨a, ha⟩ := P.exists_positive_digit x.depth h
  let y : Node P :=
    ⟨⟨⟨x.depth + 1, by omega⟩, appendDigit x.word a⟩,
      (legal_append_iff x.word a).2 ⟨x.2, h, ha⟩⟩
  refine ⟨y, ?_, rfl⟩
  exact ⟨[a], rfl⟩

/-- T09. -/
theorem cylinder_nonempty (x : Node P) : (cylinder x).Nonempty := by
  obtain ⟨s, hs, hxs⟩ := legal_full_extension x.2
  exact ⟨⟨s, hs⟩, hxs⟩

/-- T10. -/
theorem cylinder_mono {x y : Node P} (hxy : x.IsPrefix y) : cylinder y ⊆ cylinder x := by
  intro s hys
  exact hxy.trans hys

/-- T11. -/
theorem cylinders_overlap_iff (x y : Node P) :
    (cylinder x ∩ cylinder y).Nonempty ↔ x.IsPrefix y ∨ y.IsPrefix x := by
  constructor
  · rintro ⟨s, hxs, hys⟩
    exact List.prefix_or_prefix_of_prefix hxs hys
  · rintro (hxy | hyx)
    · obtain ⟨s, hs⟩ := cylinder_nonempty y
      exact ⟨s, cylinder_mono hxy hs, hs⟩
    · obtain ⟨s, hs⟩ := cylinder_nonempty x
      exact ⟨s, hs, cylinder_mono hyx hs⟩

/-- T12. -/
theorem antichain_disjoint {U : Set (Node P)} (hU : PrefixAntichain U)
    {x y : Node P} (hx : x ∈ U) (hy : y ∈ U) (hne : x ≠ y) :
    Disjoint (cylinder x) (cylinder y) := by
  apply Set.disjoint_left.mpr
  intro s hxs hys
  rcases List.prefix_or_prefix_of_prefix hxs hys with hxy | hyx
  · exact hne (hU x hx y hy hxy)
  · exact hne (hU y hy x hx hyx).symm

/-- T13. -/
theorem antichain_cover_unique {U : Set (Node P)} (hU : PrefixAntichain U)
    (hcover : Covers U) (s : FullWord P) : ∃! x : Node P, x ∈ U ∧ s ∈ cylinder x := by
  obtain ⟨x, hx, hxs⟩ := hcover s
  refine ⟨x, ⟨hx, hxs⟩, ?_⟩
  rintro y ⟨hy, hys⟩
  rcases List.prefix_or_prefix_of_prefix hxs hys with hxy | hyx
  · exact (hU x hx y hy hxy).symm
  · exact hU y hy x hx hyx

/-- T14. -/
theorem cylinder_children (x : Node P) (h : x.depth < K) (s : FullWord P) :
    s ∈ cylinder x ↔ ∃ y : Node P, Child x y ∧ s ∈ cylinder y := by
  constructor
  · intro hxs
    have hd : x.depth + 1 ≤ K := by omega
    let yw : Word k (x.depth + 1) := truncate hd s.1
    have hyw : Legal P yw := legal_truncate s.2 hd
    let y : Node P := ⟨⟨⟨x.depth + 1, by omega⟩, yw⟩, hyw⟩
    have hys : Prefix yw s.1 := truncate_prefix hd s.1
    have hxy : Prefix x.word yw :=
      List.prefix_of_prefix_length_le hxs hys
        (by simpa only [List.Vector.toList_length] using Nat.le_succ x.depth)
    exact ⟨y, ⟨hxy, rfl⟩, hys⟩
  · rintro ⟨y, hxy, hys⟩
    exact hxy.1.trans hys

/-- T15. -/
instance tree_finite (P : PileProfile N k K) : Finite (Node P) :=
  inferInstanceAs (Finite {x : RawPrefix k K // Legal P x.2})

end RiffleShuffle
