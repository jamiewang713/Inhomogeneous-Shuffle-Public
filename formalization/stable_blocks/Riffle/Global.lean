import Riffle.SourceStable
import Riffle.Retention

/-! Frozen G01--G03: exact global boundary decomposition and its rank intervals. -/
namespace Riffle

/-- A sampled full word in a stable cylinder has the indexed boundary pair. -/
theorem stable_cylinder_fiber {D : Model} {A : Setup D} {y z x ω : Word}
    (hp : RawPair A y z) (hx : x ∈ Stable A y z) (hω : ω ∈ Cylinder D x) :
    ω ∈ Cylinder D A.w ∧ selected A .left ω = y ∧ selected A .right ω = z := by
  have hvω : ω ∈ Cylinder D (join y z) :=
    ⟨hω.1, (stable_desc hp hx).2.trans hω.2⟩
  rwa [← boundary_pair_fiber hp] at hvω

/-- G01: retention removes no further strings after the two admissibility tests. -/
theorem retained_stable_coverage_iff {D : Model} {A : Setup D} {ω : Word}
    (hω : ω ∈ Cylinder D A.w) :
    (∃ y z x, AdmissiblePair A y z ∧ Retained A y z ∧
      x ∈ Stable A y z ∧ ω ∈ Cylinder D x) ↔
    selected A .left ω ∈ Admissible A .left ∧
      selected A .right ω ∈ Admissible A .right := by
  constructor
  · rintro ⟨y, z, x, hp, _, hx, hxω⟩
    have hf := stable_cylinder_fiber (admissiblePair_rawPair hp) hx hxω
    exact ⟨hf.2.1.symm ▸ hp.1, hf.2.2.symm ▸ hp.2.1⟩
  · intro hgood
    have hp := selected_rawPair hω
    have hvω : ω ∈ Cylinder D (join (selected A .left ω) (selected A .right ω)) := by
      rw [← boundary_pair_fiber hp]
      exact ⟨hω, rfl, rfl⟩
    obtain ⟨x, hx, hxω⟩ := stable_exists_prefix hp hvω
    exact ⟨_, _, x, ⟨hgood.1, hgood.2, hp.2.2⟩, rawPair_retained hp, hx, hω.1, hxω⟩

/-- G01: an indexed stable cylinder is unique, including both boundary components. -/
theorem stable_index_unique {D : Model} {A : Setup D} {y z x y' z' x' ω : Word}
    (hp : RawPair A y z) (hp' : RawPair A y' z')
    (hx : x ∈ Stable A y z) (hx' : x' ∈ Stable A y' z')
    (hω : ω ∈ Cylinder D x) (hω' : ω ∈ Cylinder D x') :
    y = y' ∧ z = z' ∧ x = x' := by
  have hf := stable_cylinder_fiber hp hx hω
  have hf' := stable_cylinder_fiber hp' hx' hω'
  have hy : y = y' := hf.2.1.symm.trans hf'.2.1
  have hz : z = z' := hf.2.2.symm.trans hf'.2.2
  subst y'
  subst z'
  refine ⟨rfl, rfl, ?_⟩
  rcases prefixes_comparable hω.2 hω'.2 with h | h
  · exact stable_antichain hp x hx x' hx' h
  · exact (stable_antichain hp x' hx' x hx h).symm

theorem retained_stable_existsUnique {D : Model} {A : Setup D} {ω : Word}
    (hω : ω ∈ Cylinder D A.w)
    (hgood : selected A .left ω ∈ Admissible A .left ∧
      selected A .right ω ∈ Admissible A .right) :
    ∃! t : Word × Word × Word,
      AdmissiblePair A t.1 t.2.1 ∧ Retained A t.1 t.2.1 ∧
      t.2.2 ∈ Stable A t.1 t.2.1 ∧ ω ∈ Cylinder D t.2.2 := by
  obtain ⟨y, z, x, hp, hr, hx, hxω⟩ := (retained_stable_coverage_iff hω).mpr hgood
  refine ⟨(y, z, x), ⟨hp, hr, hx, hxω⟩, ?_⟩
  rintro ⟨y', z', x'⟩ ⟨hp', _, hx', hxω'⟩
  have he := stable_index_unique (admissiblePair_rawPair hp') (admissiblePair_rawPair hp)
    hx' hx hxω' hxω
  exact Prod.ext he.1 (Prod.ext he.2.1 he.2.2)

/-- G02: the exact source global boundary decomposition after admissibility. -/
theorem global_boundary_decomposition {D : Model} (A : Setup D) :
    {ω | ∃ y z x, AdmissiblePair A y z ∧ Retained A y z ∧
      x ∈ Stable A y z ∧ ω ∈ Cylinder D x} =
    {ω | ω ∈ Cylinder D A.w ∧ selected A .left ω ∈ Admissible A .left ∧
      selected A .right ω ∈ Admissible A .right} := by
  ext ω
  constructor
  · intro h
    have hcopy := h
    obtain ⟨y, z, x, hp, _, hx, hxω⟩ := h
    have hw := (stable_cylinder_fiber (admissiblePair_rawPair hp) hx hxω).1
    exact ⟨hw, (retained_stable_coverage_iff hw).mp hcopy⟩
  · rintro ⟨hw, hgood⟩
    exact (retained_stable_coverage_iff hw).mpr hgood

/-- G02: distinct triples give disjoint cylinders. -/
theorem global_stable_disjoint {D : Model} {A : Setup D} {y z x y' z' x' : Word}
    (hp : AdmissiblePair A y z) (_hr : Retained A y z) (hx : x ∈ Stable A y z)
    (hp' : AdmissiblePair A y' z') (_hr' : Retained A y' z') (hx' : x' ∈ Stable A y' z')
    (hne : (y, z, x) ≠ (y', z', x')) : Disjoint (Cylinder D x) (Cylinder D x') := by
  apply Set.disjoint_left.mpr
  intro ω hω hω'
  have he := stable_index_unique (admissiblePair_rawPair hp) (admissiblePair_rawPair hp')
    hx hx' hω hω'
  exact hne (Prod.ext he.1 (Prod.ext he.2.1 he.2.2))

/-- G02: the only omitted ambient strings fail a boundary admissibility test. -/
theorem omitted_iff_inadmissible {D : Model} {A : Setup D} {ω : Word}
    (hω : ω ∈ Cylinder D A.w) :
    (¬∃ y z x, AdmissiblePair A y z ∧ Retained A y z ∧
      x ∈ Stable A y z ∧ ω ∈ Cylinder D x) ↔
    selected A .left ω ∉ Admissible A .left ∨
      selected A .right ω ∉ Admissible A .right := by
  rw [retained_stable_coverage_iff hω]
  exact not_and_or

/-- G02: before truncation no full ambient string is omitted. -/
theorem global_raw_stable_decomposition {D : Model} (A : Setup D) :
    {ω | ∃ y z x, RawPair A y z ∧ Retained A y z ∧
      x ∈ Stable A y z ∧ ω ∈ Cylinder D x} = Cylinder D A.w := by
  ext ω
  constructor
  · rintro ⟨y, z, x, hp, _, hx, hxω⟩
    exact (stable_cylinder_fiber hp hx hxω).1
  · intro hω
    obtain ⟨y, z, hp, hvω⟩ := raw_boundary_cover hω
    obtain ⟨x, hx, hxω⟩ := stable_exists_prefix hp hvω
    exact ⟨y, z, x, hp, rawPair_retained hp, hx, hω.1, hxω⟩

/-- G03: exact global cover for rank sets, allowing empty pieces. -/
theorem global_boundary_rankSet {D : Model} (A : Setup D) {M : ℕ}
    (rows : Fin M → Word) :
    {i | ∃ y z x, AdmissiblePair A y z ∧ Retained A y z ∧
      x ∈ Stable A y z ∧ i ∈ RankSet rows (Cylinder D x)} =
    {i | rows i ∈ Cylinder D A.w ∧ selected A .left (rows i) ∈ Admissible A .left ∧
      selected A .right (rows i) ∈ Admissible A .right} := by
  ext i
  exact Set.ext_iff.mp (global_boundary_decomposition A) (rows i)

theorem global_stable_intervals_disjoint {D : Model} {A : Setup D} {M : ℕ}
    (rows : Fin M → Word) {y z x y' z' x' : Word}
    (hp : AdmissiblePair A y z) (hr : Retained A y z) (hx : x ∈ Stable A y z)
    (hp' : AdmissiblePair A y' z') (hr' : Retained A y' z') (hx' : x' ∈ Stable A y' z')
    (hne : (y, z, x) ≠ (y', z', x')) :
    Disjoint (RankSet rows (Cylinder D x)) (RankSet rows (Cylinder D x')) :=
  rankSet_disjoint rows (global_stable_disjoint hp hr hx hp' hr' hx' hne)

theorem global_stable_intervals_convex {D : Model} {A : Setup D} {M : ℕ}
    (rows : Fin M → Word) (hfull : ∀ i, Full D (rows i)) (hsorted : SortedRows rows)
    {y z x : Word} (_hp : AdmissiblePair A y z) (_hr : Retained A y z)
    (_hx : x ∈ Stable A y z) : Set.OrdConnected (RankSet rows (Cylinder D x)) :=
  rankSet_cylinder_convex hfull hsorted x

theorem omitted_rank_iff_inadmissible {D : Model} {A : Setup D} {M : ℕ}
    (rows : Fin M → Word) {i : Fin M} (hi : rows i ∈ Cylinder D A.w) :
    (¬∃ y z x, AdmissiblePair A y z ∧ Retained A y z ∧
      x ∈ Stable A y z ∧ i ∈ RankSet rows (Cylinder D x)) ↔
    selected A .left (rows i) ∉ Admissible A .left ∨
      selected A .right (rows i) ∉ Admissible A .right :=
  omitted_iff_inadmissible hi

end Riffle
