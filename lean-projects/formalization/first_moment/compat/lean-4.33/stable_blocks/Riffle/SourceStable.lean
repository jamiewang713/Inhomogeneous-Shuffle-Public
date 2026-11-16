import Riffle.Stopping
import Riffle.Cost

/-! Frozen catalog S03--S05, with persistence proved from the pile model. -/
namespace Riffle

theorem stop_join_persistent {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) {x u : Word}
    (hx : x ∈ Desc D (join y z)) (hu : u ∈ Desc D (join y z))
    (hxu : x <+: u) (hs : Stop A y z x) : Stop A y z u := by
  have hv := rawPair_join_desc hp
  exact stop_persistent ⟨hx.1, hv.2.trans hx.2⟩ ⟨hu.1, hv.2.trans hu.2⟩ hxu hs

theorem stable_antichain {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) : PrefixAntichain (Stable A y z) := by
  rw [stable_eq_genericCut hp]
  exact genericCut_antichain (rawPair_join_desc hp).1 (stop_join_persistent hp)

theorem stable_existsUnique_prefix {D : Model} {A : Setup D} {y z ω : Word}
    (hp : RawPair A y z) (hω : ω ∈ Cylinder D (join y z)) :
    ∃! x, x ∈ Stable A y z ∧ x <+: ω := by
  rw [stable_eq_genericCut hp]
  exact genericCut_existsUnique_prefix (rawPair_join_desc hp).1
    (stop_join_persistent hp) hω

theorem stable_cylinder_disjoint {D : Model} {A : Setup D} {y z x u : Word}
    (hp : RawPair A y z) (hx : x ∈ Stable A y z) (hu : u ∈ Stable A y z)
    (hne : x ≠ u) : Disjoint (Cylinder D x) (Cylinder D u) :=
  antichain_cylinder_disjoint (stable_antichain hp) hx hu hne

theorem gamma_first_crossing {D : Model} {A : Setup D} {y z x : Word}
    (hp : RawPair A y z) (hroot : ¬Stop A y z (join y z))
    (hx : x ∈ Gamma A y z) :
    (join y z).length < x.length ∧ parent x ∈ Desc D A.w ∧
      ¬Stop A y z (parent x) ∧
      ∀ u, u ∈ Desc D (join y z) → u <+: parent x → ¬Stop A y z u := by
  have hxD : x ∈ Desc D (join y z) := by
    rw [← pairDesc_eq hp.1.1 hp.2.1.1 hp.2.2]
    exact hx.1
  have hvx : (join y z).length < x.length := by
    have hle := hxD.2.length_le
    by_contra hn
    have heq : join y z = x := hxD.2.eq_of_length (by omega)
    exact hroot (heq.symm ▸ hx.2.1)
  have hparD : parent x ∈ Desc D (join y z) :=
    ⟨parent_legal hxD.1, prefix_parent hxD.2 hvx⟩
  have hparA : parent x ∈ Desc D A.w :=
    ⟨hparD.1, (rawPair_join_desc hp).2.trans hparD.2⟩
  refine ⟨hvx, hparA, hx.2.2, ?_⟩
  intro u hu hup hqu
  exact hx.2.2 (stop_join_persistent hp hu hparD hup hqu)

theorem lambda_no_crossing_iff {D : Model} {A : Setup D} {y z x : Word}
    (hp : RawPair A y z) (hx : x ∈ pairDesc A y z) (hlen : x.length = D.K) :
    x ∈ Lambda A y z ↔
      ∀ u, u ∈ Desc D (join y z) → u <+: x → ¬Stop A y z u := by
  have hxD : x ∈ Desc D (join y z) := by
    rw [← pairDesc_eq hp.1.1 hp.2.1.1 hp.2.2]
    exact hx
  simp only [Lambda, Set.mem_setOf_eq, hx, hlen, true_and]
  exact genericCut_fallback_iff hxD (stop_join_persistent hp)

theorem lambda_full {D : Model} {A : Setup D} {y z x : Word}
    (hx : x ∈ Lambda A y z) : Full D x :=
  ⟨hx.1.1.1, hx.2.1⟩

theorem gamma_no_later_stable {D : Model} {A : Setup D} {y z x u : Word}
    (hp : RawPair A y z) (hroot : ¬Stop A y z (join y z))
    (hx : x ∈ Gamma A y z) (hu : u ∈ Stable A y z) (hxu : x <+: u) : x = u := by
  have hlt := (gamma_first_crossing hp hroot hx).1
  have hnt : ¬Terminal D y z := by
    intro ht
    have hj := (terminal_iff_join_length hp.1.1.1 hp.2.1.1.1).mp ht
    have hxlen := hx.1.1.1.1
    omega
  have hxs : x ∈ Stable A y z := by
    simp only [Stable, if_neg hnt, if_neg hroot, Set.mem_union]
    exact Or.inl hx
  exact stable_antichain hp x hxs u hu hxu

theorem stable_ambient_terminal {D : Model} {A : Setup D} {ω : Word}
    (hw : A.w.length = D.K) (hω : ω ∈ Cylinder D A.w) :
    selected A .left ω = A.w ∧ selected A .right ω = A.w ∧
      Stable A (selected A .left ω) (selected A .right ω) = {A.w} := by
  have hl := selected_ambient_terminal Side.left hw hω
  have hr := selected_ambient_terminal Side.right hw hω
  refine ⟨hl, hr, ?_⟩
  rw [hl, hr, stable_terminal A A.w A.w (Or.inl hw)]
  simp [join]

theorem stable_partition {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) (_hr : Retained A y z) :
    PrefixAntichain (Stable A y z) ∧
      FamilyCylinder D (Stable A y z) = Cylinder D (join y z) ∧
      (∀ ω ∈ Cylinder D (join y z), ∃! x, x ∈ Stable A y z ∧ x <+: ω) ∧
      (∀ x ∈ Stable A y z, ∀ u ∈ Stable A y z, x ≠ u →
        Disjoint (Cylinder D x) (Cylinder D u)) := by
  exact ⟨stable_antichain hp, stable_cover hp,
    fun _ hω => stable_existsUnique_prefix hp hω,
    fun _ hx _ hu hne => stable_cylinder_disjoint hp hx hu hne⟩

theorem stable_rankSet_cover {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) {M : ℕ} (rows : Fin M → Word) :
    (⋃ x ∈ Stable A y z, RankSet rows (Cylinder D x)) =
      RankSet rows (Cylinder D (join y z)) := by
  ext i
  simp only [Set.mem_iUnion, RankSet, Set.mem_preimage, exists_prop]
  change rows i ∈ FamilyCylinder D (Stable A y z) ↔ _
  rw [stable_cover hp]

theorem stable_intervals_partition {D : Model} {A : Setup D} {y z : Word}
    (hp : RawPair A y z) (_hr : Retained A y z) {M : ℕ} (rows : Fin M → Word)
    (hfull : ∀ i, Full D (rows i)) (hsorted : SortedRows rows) :
    (∀ x ∈ Stable A y z, Set.OrdConnected (RankSet rows (Cylinder D x))) ∧
      (∀ x ∈ Stable A y z, ∀ u ∈ Stable A y z, x ≠ u →
        Disjoint (RankSet rows (Cylinder D x)) (RankSet rows (Cylinder D u))) ∧
      (⋃ x ∈ Stable A y z, RankSet rows (Cylinder D x)) =
        RankSet rows (Cylinder D (join y z)) := by
  exact ⟨fun x _ => rankSet_cylinder_convex hfull hsorted x,
    fun _ hx _ hu hne => rankSet_disjoint rows (stable_cylinder_disjoint hp hx hu hne),
    stable_rankSet_cover hp rows⟩

end Riffle
