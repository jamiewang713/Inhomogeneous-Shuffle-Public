import Riffle.Words

/-! First-crossing boundary cuts, including terminal fallback and pair fibers.
All statements instantiate the frozen W04 and B02–B05 schemas. -/
namespace Riffle

theorem boundaryCut_mem_desc {D : Model} {w x : Word} {q : ℕ → ℕ → Prop}
    (hx : x ∈ BoundaryCut D w q) : x ∈ Desc D w := hx.1

theorem boundaryCut_nonterminal {D : Model} {w x : Word} {q : ℕ → ℕ → Prop}
    (hx : x ∈ BoundaryCut D w q) (ht : x.length ≠ D.K) :
    w.length < x.length ∧ q (x.length - 1) (digit x (x.length - 1)) ∧
      ∀ i, w.length ≤ i → i < x.length - 1 → ¬q i (digit x i) := by
  rcases hx.2 with h | h
  · exact h
  · exact (ht h.1).elim

theorem boundaryCut_antichain (D : Model) (w : Word) (q : ℕ → ℕ → Prop) :
    PrefixAntichain (BoundaryCut D w q) := by
  intro x hx y hy hxy
  by_cases he : x.length = y.length
  · exact hxy.eq_of_length he
  have hlt : x.length < y.length := by
    have := hxy.length_le
    omega
  rcases hx.2 with hx | hx
  · have hiw : w.length ≤ x.length - 1 := by omega
    have hix : x.length - 1 < x.length := by omega
    have hd := digit_prefix hxy hix
    rcases hy.2 with hy | hy
    · have hiy : x.length - 1 < y.length - 1 := by omega
      exact (hy.2.2 _ hiw hiy (hd ▸ hx.2.1)).elim
    · have hiK : x.length - 1 < D.K := by omega
      exact (hy.2 _ hiw hiK (hd ▸ hx.2.1)).elim
  · have hyK := hy.1.1.1
    omega

theorem selectCut_spec {D : Model} {w ω : Word} (q : ℕ → ℕ → Prop)
    (hω : ω ∈ Cylinder D w) :
    selectCut D w q ω ∈ BoundaryCut D w q ∧ selectCut D w q ω <+: ω := by
  classical
  by_cases h : ∃ i, w.length ≤ i ∧ i < D.K ∧ q i (digit ω i)
  · rw [selectCut, dif_pos h]
    have hs := Nat.find_spec h
    have hm : Nat.find h + 1 ≤ ω.length := by
      have hlen := hω.1.2
      omega
    have hlen : (ω.take (Nat.find h + 1)).length = Nat.find h + 1 :=
      List.length_take_of_le hm
    have hp : ω.take (Nat.find h + 1) <+: ω := List.take_prefix _ _
    refine ⟨⟨⟨legal_take hω.1.1 _, ?_⟩, Or.inl ?_⟩, hp⟩
    · exact List.prefix_of_prefix_length_le hω.2 hp (by omega)
    · rw [hlen]
      refine ⟨by omega, ?_, ?_⟩
      · simpa only [Nat.add_sub_cancel, digit_take (Nat.lt_succ_self _)] using hs.2.2
      · intro i hiw hil
        have hil' : i < Nat.find h := by omega
        have hid : digit (ω.take (Nat.find h + 1)) i = digit ω i :=
          digit_take (by omega)
        rw [hid]
        intro hq
        exact Nat.find_min h hil' ⟨hiw, by omega, hq⟩
  · rw [selectCut, dif_neg h]
    have he : ω.take D.K = ω := by rw [← hω.1.2, List.take_length]
    rw [he]
    refine ⟨⟨⟨hω.1.1, hω.2⟩, Or.inr ⟨hω.1.2, ?_⟩⟩, List.prefix_rfl⟩
    intro i hiw hiK hq
    exact h ⟨i, hiw, hiK, hq⟩

theorem boundaryCut_unique_prefix {D : Model} {w ω x : Word}
    {q : ℕ → ℕ → Prop} (hω : ω ∈ Cylinder D w)
    (hx : x ∈ BoundaryCut D w q) (hxp : x <+: ω) :
    x = selectCut D w q ω := by
  have hs := selectCut_spec q hω
  rcases List.prefix_or_prefix_of_prefix hxp hs.2 with h | h
  · exact boundaryCut_antichain D w q x hx _ hs.1 h
  · exact (boundaryCut_antichain D w q _ hs.1 x hx h).symm

theorem boundaryCut_existsUnique {D : Model} {w ω : Word} (q : ℕ → ℕ → Prop)
    (hω : ω ∈ Cylinder D w) :
    ∃! x, x ∈ BoundaryCut D w q ∧ x <+: ω := by
  refine ⟨selectCut D w q ω, selectCut_spec q hω, ?_⟩
  intro x hx
  exact boundaryCut_unique_prefix hω hx.1 hx.2

theorem selectCut_eq_of_no_cross {D : Model} {w ω : Word}
    (q : ℕ → ℕ → Prop) (hω : ω ∈ Cylinder D w)
    (hno : ∀ i, w.length ≤ i → i < D.K → ¬q i (digit ω i)) :
    selectCut D w q ω = ω := by
  classical
  have h : ¬∃ i, w.length ≤ i ∧ i < D.K ∧ q i (digit ω i) := by
    rintro ⟨i, hiw, hiK, hq⟩
    exact hno i hiw hiK hq
  rw [selectCut, dif_neg h, ← hω.1.2, List.take_length]

theorem selectCut_first_crossing {D : Model} {w ω : Word}
    (q : ℕ → ℕ → Prop) (hω : ω ∈ Cylinder D w)
    (h : ∃ i, w.length ≤ i ∧ i < D.K ∧ q i (digit ω i)) :
    w.length < (selectCut D w q ω).length ∧
    q ((selectCut D w q ω).length - 1)
      (digit ω ((selectCut D w q ω).length - 1)) ∧
    (∀ i, w.length ≤ i → i < (selectCut D w q ω).length - 1 →
      ¬q i (digit ω i)) ∧
    (∀ i, w.length ≤ i → i < D.K → q i (digit ω i) →
      (selectCut D w q ω).length - 1 ≤ i) := by
  classical
  rw [selectCut, dif_pos h]
  have hs := Nat.find_spec h
  have hm : Nat.find h + 1 ≤ ω.length := by have := hω.1.2; omega
  rw [List.length_take_of_le hm]
  simp only [Nat.add_sub_cancel]
  refine ⟨by omega, hs.2.2, ?_, ?_⟩
  · intro i hiw hil hq
    exact Nat.find_min h hil ⟨hiw, by omega, hq⟩
  · intro i hiw hiK hq
    exact Nat.find_min' h ⟨hiw, hiK, hq⟩

theorem boundary_mem_desc {D : Model} {A : Setup D} {s : Side} {x : Word}
    (hx : x ∈ Boundary A s) : x ∈ Desc D A.w := hx.1

theorem boundary_nonterminal {D : Model} {A : Setup D} {s : Side} {x : Word}
    (hx : x ∈ Boundary A s) (ht : x.length ≠ D.K) :
    A.w.length < x.length ∧ Cross A s x (x.length - 1) ∧
    ∀ i, A.w.length ≤ i → i < x.length - 1 → ¬Cross A s x i :=
  boundaryCut_nonterminal hx ht

theorem boundary_antichain {D : Model} (A : Setup D) (s : Side) :
    PrefixAntichain (Boundary A s) := boundaryCut_antichain D A.w (crossDigit A s)

theorem admissible_mem_boundary {D : Model} {A : Setup D} {s : Side} {x : Word}
    (hx : x ∈ Admissible A s) : x ∈ Boundary A s := hx.1

theorem admissible_antichain {D : Model} (A : Setup D) (s : Side) :
    PrefixAntichain (Admissible A s) := by
  intro x hx y hy hxy
  exact boundary_antichain A s x hx.1 y hy.1 hxy

theorem admissiblePair_rawPair {D : Model} {A : Setup D} {y z : Word}
    (h : AdmissiblePair A y z) : RawPair A y z := ⟨h.1.1, h.2.1.1, h.2.2⟩

theorem selected_spec {D : Model} {A : Setup D} (s : Side) {ω : Word}
    (hω : ω ∈ Cylinder D A.w) :
    selected A s ω ∈ Boundary A s ∧ selected A s ω <+: ω :=
  selectCut_spec (crossDigit A s) hω

theorem selected_unique {D : Model} {A : Setup D} {s : Side} {ω x : Word}
    (hω : ω ∈ Cylinder D A.w) (hx : x ∈ Boundary A s) (hp : x <+: ω) :
    x = selected A s ω := boundaryCut_unique_prefix hω hx hp

theorem selected_existsUnique {D : Model} {A : Setup D} (s : Side) {ω : Word}
    (hω : ω ∈ Cylinder D A.w) :
    ∃! x, x ∈ Boundary A s ∧ x <+: ω :=
  boundaryCut_existsUnique (crossDigit A s) hω

theorem selected_eq_iff {D : Model} {A : Setup D} {s : Side} {ω x : Word}
    (hω : ω ∈ Cylinder D A.w) (hx : x ∈ Boundary A s) :
    selected A s ω = x ↔ ω ∈ Cylinder D x := by
  constructor
  · intro h
    exact ⟨hω.1, h ▸ (selected_spec s hω).2⟩
  · intro h
    exact (selected_unique hω hx h.2).symm

theorem rawPair_join_desc {D : Model} {A : Setup D} {y z : Word}
    (h : RawPair A y z) : join y z ∈ Desc D A.w := by
  unfold join
  split_ifs
  · exact boundary_mem_desc h.1
  · exact boundary_mem_desc h.2.1

theorem rawPair_prefix_join {D : Model} {A : Setup D} {y z : Word}
    (h : RawPair A y z) : y <+: join y z ∧ z <+: join y z := by
  rcases h.2.2 with ⟨x, hx⟩
  unfold join
  split_ifs with hlen
  · exact ⟨List.prefix_rfl, List.prefix_of_prefix_length_le hx.2.2 hx.2.1 hlen⟩
  · exact ⟨List.prefix_of_prefix_length_le hx.2.1 hx.2.2 (by omega), List.prefix_rfl⟩

theorem boundary_pair_fiber {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) :
    {ω | ω ∈ Cylinder D A.w ∧ selected A .left ω = y ∧
      selected A .right ω = z} = Cylinder D (join y z) := by
  ext ω
  constructor
  · rintro ⟨hω, hl, hr⟩
    have hyl := ((selected_eq_iff hω hp.1).mp hl).2
    have hzr := ((selected_eq_iff hω hp.2.1).mp hr).2
    refine ⟨hω.1, ?_⟩
    unfold join
    split_ifs
    · exact hyl
    · exact hzr
  · intro hω
    have hw : ω ∈ Cylinder D A.w :=
      ⟨hω.1, (rawPair_join_desc hp).2.trans hω.2⟩
    have hj := rawPair_prefix_join hp
    exact ⟨hw, (selected_eq_iff hw hp.1).mpr ⟨hω.1, hj.1.trans hω.2⟩,
      (selected_eq_iff hw hp.2.1).mpr ⟨hω.1, hj.2.trans hω.2⟩⟩

theorem incompatible_boundary_fiber_empty {D : Model} {A : Setup D} {y z : Word}
    (hinc : ¬Compatible A y z) :
    {ω | ω ∈ Cylinder D A.w ∧ selected A .left ω = y ∧
      selected A .right ω = z} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ω ⟨hω, hl, hr⟩
  have hyl : y <+: ω := hl ▸ (selected_spec .left hω).2
  have hzr : z <+: ω := hr ▸ (selected_spec .right hω).2
  exact hinc ⟨ω, ⟨hω.1.1, hω.2⟩, hyl, hzr⟩

theorem rawPair_join_antichain {D : Model} {A : Setup D} {y z y' z' : Word}
    (hp : RawPair A y z) (hp' : RawPair A y' z')
    (hjoin : join y z <+: join y' z') : y = y' ∧ z = z' := by
  have h := rawPair_prefix_join hp
  have h' := rawPair_prefix_join hp'
  constructor
  · rcases List.prefix_or_prefix_of_prefix (h.1.trans hjoin) h'.1 with hc | hc
    · exact boundary_antichain A .left y hp.1 y' hp'.1 hc
    · exact (boundary_antichain A .left y' hp'.1 y hp.1 hc).symm
  · rcases List.prefix_or_prefix_of_prefix (h.2.trans hjoin) h'.2 with hc | hc
    · exact boundary_antichain A .right z hp.2.1 z' hp'.2.1 hc
    · exact (boundary_antichain A .right z' hp'.2.1 z hp.2.1 hc).symm

theorem rawPair_cylinders_disjoint {D : Model} {A : Setup D} {y z y' z' : Word}
    (hp : RawPair A y z) (hp' : RawPair A y' z') (hne : (y, z) ≠ (y', z')) :
    Disjoint (Cylinder D (join y z)) (Cylinder D (join y' z')) := by
  apply Set.disjoint_left.mpr
  intro ω hω hω'
  have hf : ω ∈ {ω | ω ∈ Cylinder D A.w ∧ selected A .left ω = y ∧
      selected A .right ω = z} := by rwa [boundary_pair_fiber hp]
  have hf' : ω ∈ {ω | ω ∈ Cylinder D A.w ∧ selected A .left ω = y' ∧
      selected A .right ω = z'} := by rwa [boundary_pair_fiber hp']
  exact hne (Prod.ext (hf.2.1.symm.trans hf'.2.1) (hf.2.2.symm.trans hf'.2.2))

theorem selected_rawPair {D : Model} {A : Setup D} {ω : Word}
    (hω : ω ∈ Cylinder D A.w) :
    RawPair A (selected A .left ω) (selected A .right ω) := by
  have hl := selected_spec .left hω
  have hr := selected_spec .right hω
  exact ⟨hl.1, hr.1, ⟨ω, ⟨hω.1.1, hω.2⟩, hl.2, hr.2⟩⟩

theorem raw_boundary_cover {D : Model} {A : Setup D} {ω : Word}
    (hω : ω ∈ Cylinder D A.w) :
    ∃ y z, RawPair A y z ∧ ω ∈ Cylinder D (join y z) := by
  have hp := selected_rawPair hω
  refine ⟨selected A .left ω, selected A .right ω, hp, ?_⟩
  rw [← boundary_pair_fiber hp]
  exact ⟨hω, rfl, rfl⟩

theorem raw_boundary_union {D : Model} (A : Setup D) :
    {ω | ∃ y z, RawPair A y z ∧ ω ∈ Cylinder D (join y z)} = Cylinder D A.w := by
  ext ω
  constructor
  · rintro ⟨y, z, hp, hω⟩
    exact ⟨hω.1, (rawPair_join_desc hp).2.trans hω.2⟩
  · exact raw_boundary_cover

theorem boundary_ambient_terminal {D : Model} {A : Setup D} (s : Side)
    (h : A.w.length = D.K) : A.w ∈ Boundary A s := by
  refine ⟨⟨A.w_legal, List.prefix_rfl⟩, Or.inr ⟨h, ?_⟩⟩
  intro i hiw hiK
  omega

theorem selected_ambient_terminal {D : Model} {A : Setup D} (s : Side)
    (h : A.w.length = D.K) {ω : Word} (hω : ω ∈ Cylinder D A.w) :
    selected A s ω = A.w :=
  (selected_eq_iff hω (boundary_ambient_terminal s h)).mpr hω

end Riffle
