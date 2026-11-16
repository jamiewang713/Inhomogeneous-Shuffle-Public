import Riffle.Boundary

/-! Frozen catalog S02: finite stopping with a persistent predicate. -/
namespace Riffle

theorem genericCut_of_root {D : Model} {v : Word} {Q : Word → Prop}
    (h : Q v ∨ v.length = D.K) : GenericCut D v Q = {v} := by
  classical
  simp [GenericCut, h]

theorem genericCut_of_not_root {D : Model} {v : Word} {Q : Word → Prop}
    (hq : ¬Q v) (hl : v.length ≠ D.K) :
    GenericCut D v Q =
      {x | x ∈ Desc D v ∧ ((Q x ∧ ¬Q (parent x)) ∨ (x.length = D.K ∧ ¬Q x))} := by
  classical
  simp [GenericCut, hq, hl]

theorem genericCut_desc {D : Model} {v x : Word} {Q : Word → Prop}
    (hv : Legal D v) (hx : x ∈ GenericCut D v Q) : x ∈ Desc D v := by
  classical
  by_cases h : Q v ∨ v.length = D.K
  · rw [genericCut_of_root h] at hx
    have hxeq : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨hv, List.prefix_rfl⟩
  · simp only [GenericCut, if_neg h, Set.mem_setOf_eq] at hx
    exact hx.1

theorem genericCut_antichain {D : Model} {v : Word} {Q : Word → Prop}
    (_hv : Legal D v)
    (hQ : ∀ {x y : Word}, x ∈ Desc D v → y ∈ Desc D v → x <+: y → Q x → Q y) :
    PrefixAntichain (GenericCut D v Q) := by
  classical
  by_cases h : Q v ∨ v.length = D.K
  · rw [genericCut_of_root h]
    intro x hx y hy _
    simpa only [Set.mem_singleton_iff] using hx.trans hy.symm
  · simp only [GenericCut, if_neg h]
    intro x hx y hy hxy
    rcases hx with ⟨hxD, hxQ | hxT⟩
    · rcases hy with ⟨hyD, hyQ | hyT⟩
      · by_cases heq : x.length = y.length
        · exact hxy.eq_of_length heq
        · have hlt : x.length < y.length := by
            have := hxy.length_le
            omega
          have hxpar : x <+: parent y := prefix_parent hxy hlt
          have hparD : parent y ∈ Desc D v :=
            ⟨parent_legal hyD.1, hxD.2.trans hxpar⟩
          exact False.elim (hyQ.2 (hQ hxD hparD hxpar hxQ.1))
      · exact False.elim (hyT.2 (hQ hxD hyD hxy hxQ.1))
    · exact hxy.eq_of_length_le (by
        have := hy.1.1.1
        omega)

theorem genericCut_exists_prefix {D : Model} {v ω : Word} {Q : Word → Prop}
    (hv : Legal D v) (hω : ω ∈ Cylinder D v) :
    ∃ x, x ∈ GenericCut D v Q ∧ x <+: ω := by
  classical
  by_cases hroot : Q v ∨ v.length = D.K
  · exact ⟨v, by rw [genericCut_of_root hroot]; simp, hω.2⟩
  have hqv : ¬Q v := fun h => hroot (Or.inl h)
  have hlv : v.length ≠ D.K := fun h => hroot (Or.inr h)
  have hωlen : ω.length = D.K := hω.1.2
  by_cases hex : ∃ m : ℕ, v.length ≤ m ∧ m ≤ D.K ∧ Q (ω.take m)
  · let m := Nat.find hex
    have hm : v.length ≤ m ∧ m ≤ D.K ∧ Q (ω.take m) := Nat.find_spec hex
    have hmlen : m ≤ ω.length := by omega
    have hxlen : (ω.take m).length = m := by simp [List.length_take, hmlen]
    have hvx : v <+: ω.take m :=
      List.prefix_of_prefix_length_le hω.2 (List.take_prefix m ω) (by omega)
    have hvm : v.length < m := by
      by_contra hnot
      have heq : v.length = m := by omega
      have hvxeq : v = ω.take m := hvx.eq_of_length (by omega)
      exact hqv (hvxeq.symm ▸ hm.2.2)
    have hpar : parent (ω.take m) = ω.take (m - 1) := by
      simp only [parent, hxlen, List.take_take]
      rw [Nat.min_eq_left (Nat.sub_le m 1)]
    have hnotpar : ¬Q (parent (ω.take m)) := by
      intro hqp
      rw [hpar] at hqp
      have hmin : m ≤ m - 1 := Nat.find_min' hex ⟨by omega, by omega, hqp⟩
      omega
    refine ⟨ω.take m, ?_, List.take_prefix m ω⟩
    rw [genericCut_of_not_root hqv hlv]
    exact ⟨⟨legal_take hω.1.1 m, hvx⟩, Or.inl ⟨hm.2.2, hnotpar⟩⟩
  · have hnq : ¬Q ω := by
      intro hq
      apply hex
      refine ⟨D.K, hv.1, le_rfl, ?_⟩
      simpa only [← hωlen, List.take_length] using hq
    refine ⟨ω, ?_, List.prefix_rfl⟩
    rw [genericCut_of_not_root hqv hlv]
    exact ⟨⟨hω.1.1, hω.2⟩, Or.inr ⟨hωlen, hnq⟩⟩

theorem genericCut_existsUnique_prefix {D : Model} {v ω : Word} {Q : Word → Prop}
    (hv : Legal D v)
    (hQ : ∀ {x y : Word}, x ∈ Desc D v → y ∈ Desc D v → x <+: y → Q x → Q y)
    (hω : ω ∈ Cylinder D v) :
    ∃! x, x ∈ GenericCut D v Q ∧ x <+: ω := by
  obtain ⟨x, hx, hxω⟩ := genericCut_exists_prefix hv hω
  refine ⟨x, ⟨hx, hxω⟩, ?_⟩
  intro y hy
  have hanti := genericCut_antichain hv hQ
  rcases List.prefix_or_prefix_of_prefix hy.2 hxω with h | h
  · exact hanti y hy.1 x hx h
  · exact (hanti x hx y hy.1 h).symm

theorem genericCut_cover {D : Model} {v : Word} {Q : Word → Prop}
    (hv : Legal D v) : FamilyCylinder D (GenericCut D v Q) = Cylinder D v := by
  ext ω
  constructor
  · rintro ⟨x, hx, hxω⟩
    exact ⟨hxω.1, (genericCut_desc hv hx).2.trans hxω.2⟩
  · intro hω
    obtain ⟨x, hx, hxω⟩ := genericCut_exists_prefix hv hω
    exact ⟨x, hx, hω.1, hxω⟩

theorem genericCut_cylinder_disjoint {D : Model} {v x y : Word} {Q : Word → Prop}
    (hv : Legal D v)
    (hQ : ∀ {a b : Word}, a ∈ Desc D v → b ∈ Desc D v → a <+: b → Q a → Q b)
    (hx : x ∈ GenericCut D v Q) (hy : y ∈ GenericCut D v Q) (hne : x ≠ y) :
    Disjoint (Cylinder D x) (Cylinder D y) := by
  exact antichain_cylinder_disjoint (genericCut_antichain hv hQ) hx hy hne

theorem genericCut_crossing_minimal {D : Model} {v x : Word} {Q : Word → Prop}
    (_hv : Legal D v) (hqv : ¬Q v) (hlv : v.length ≠ D.K)
    (hQ : ∀ {a b : Word}, a ∈ Desc D v → b ∈ Desc D v → a <+: b → Q a → Q b)
    (hx : x ∈ GenericCut D v Q) (hqx : Q x) :
    v.length < x.length ∧ parent x ∈ Desc D v ∧ ¬Q (parent x) ∧
      ∀ u, u ∈ Desc D v → u <+: parent x → ¬Q u := by
  rw [genericCut_of_not_root hqv hlv] at hx
  have hnotpar : ¬Q (parent x) := by
    rcases hx.2 with hcross | hterminal
    · exact hcross.2
    · exact False.elim (hterminal.2 hqx)
  have hvx : v.length < x.length := by
    have hle := hx.1.2.length_le
    by_contra hnot
    have heq : v = x := hx.1.2.eq_of_length (by omega)
    exact hqv (heq.symm ▸ hqx)
  have hparD : parent x ∈ Desc D v :=
    ⟨parent_legal hx.1.1, prefix_parent hx.1.2 hvx⟩
  refine ⟨hvx, hparD, hnotpar, ?_⟩
  intro u hu hup hqu
  exact hnotpar (hQ hu hparD hup hqu)

theorem genericCut_fallback_iff {D : Model} {v x : Word} {Q : Word → Prop}
    (hx : x ∈ Desc D v)
    (hQ : ∀ {a b : Word}, a ∈ Desc D v → b ∈ Desc D v → a <+: b → Q a → Q b) :
    ¬Q x ↔ ∀ u, u ∈ Desc D v → u <+: x → ¬Q u := by
  constructor
  · intro hnot u hu hup hqu
    exact hnot (hQ hu hx hup hqu)
  · intro hall hqx
    exact hall x hx List.prefix_rfl hqx

/-! Definitional portions of frozen catalog S03--S04. -/

theorem gamma_lambda_disjoint {D : Model} (A : Setup D) (y z : Word) :
    Disjoint (Gamma A y z) (Lambda A y z) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact hy.2.2 hx.2.1

theorem stable_terminal {D : Model} (A : Setup D) (y z : Word)
    (h : Terminal D y z) : Stable A y z = {join y z} := by
  simp only [Stable, if_pos h]

theorem stable_stopped {D : Model} (A : Setup D) (y z : Word)
    (h : Stop A y z (join y z)) : Stable A y z = {join y z} := by
  classical
  unfold Stable
  split <;> simp_all

theorem stable_eq_genericCut {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) :
    Stable A y z = GenericCut D (join y z) (Stop A y z) := by
  classical
  have hy : y ∈ Desc D A.w := hp.1.1
  have hz : z ∈ Desc D A.w := hp.2.1.1
  have htiff := terminal_iff_join_length hy.1 hz.1
  have hdesc := pairDesc_eq hy hz hp.2.2
  by_cases ht : Terminal D y z
  · simp [Stable, GenericCut, ht, htiff.mp ht]
  · have hlen : (join y z).length ≠ D.K := fun h => ht (htiff.mpr h)
    by_cases hs : Stop A y z (join y z)
    · simp [Stable, GenericCut, ht, hs]
    · simp only [Stable, if_neg ht, if_neg hs, GenericCut, hs, hlen,
        false_or, if_false]
      ext x
      simp only [Gamma, Lambda, Set.mem_union, Set.mem_setOf_eq, hdesc]
      tauto

theorem stable_desc {D : Model} {A : Setup D} {y z x : Word}
    (hp : RawPair A y z) (hx : x ∈ Stable A y z) : x ∈ Desc D (join y z) := by
  rw [stable_eq_genericCut hp] at hx
  exact genericCut_desc (rawPair_join_desc hp).1 hx

theorem stable_exists_prefix {D : Model} {A : Setup D} {y z ω : Word}
    (hp : RawPair A y z) (hω : ω ∈ Cylinder D (join y z)) :
    ∃ x, x ∈ Stable A y z ∧ x <+: ω := by
  rw [stable_eq_genericCut hp]
  exact genericCut_exists_prefix (rawPair_join_desc hp).1 hω

theorem stable_cover {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) : FamilyCylinder D (Stable A y z) = Cylinder D (join y z) := by
  rw [stable_eq_genericCut hp]
  exact genericCut_cover (rawPair_join_desc hp).1

end Riffle
