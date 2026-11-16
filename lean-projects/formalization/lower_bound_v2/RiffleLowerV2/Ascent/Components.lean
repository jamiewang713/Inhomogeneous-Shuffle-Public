import RiffleLowerV2.Shared.Path
import RiffleLowerV2.Model.GraphSorting

/-! Deterministic path components and retained comparison supports for LB04. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Ascent

variable {N : ℕ}

def componentSet (G : PathEdges N) (j : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => componentIndex G i = j

def retainedBoundaries (G : PathEdges N) (H : Finset (Fin N)) : PathEdges N :=
  internalEdges H \ G

def leftComponent (G : PathEdges N) (e : Fin (N-1)) : Finset (Fin N) :=
  componentSet G (componentIndex G (edgeLeft e))

def rightComponent (G : PathEdges N) (e : Fin (N-1)) : Finset (Fin N) :=
  componentSet G (componentIndex G (edgeRight e))

def boundarySupport (G : PathEdges N) (e : Fin (N-1)) : Finset (Fin N) :=
  leftComponent G e ∪ rightComponent G e

def boundaryParity (G : PathEdges N) (e : Fin (N-1)) : ℕ :=
  componentIndex G (edgeLeft e) % 2

def boundaryAscent (G : PathEdges N) (e : Fin (N-1)) (π : Permutation N) : Prop :=
  ∀ x ∈ leftComponent G e, ∀ y ∈ rightComponent G e, π x < π y

@[simp] theorem mem_componentSet (G : PathEdges N) (j : ℕ) (i : Fin N) :
    i ∈ componentSet G j ↔ componentIndex G i = j := by simp [componentSet]

@[simp] theorem mem_retainedBoundaries (G : PathEdges N) (H : Finset (Fin N))
    (e : Fin (N-1)) : e ∈ retainedBoundaries G H ↔ e ∈ internalEdges H ∧ e ∉ G := by
  simp [retainedBoundaries]

theorem componentIndex_le (G : PathEdges N) {i j : Fin N} (h : i ≤ j) :
    componentIndex G i ≤ componentIndex G j := by
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨lt_of_lt_of_le he.1 h, he.2⟩

theorem componentIndex_edge_present (G : PathEdges N) (e : Fin (N-1)) (he : e ∈ G) :
    componentIndex G (edgeRight e) = componentIndex G (edgeLeft e) := by
  unfold componentIndex
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp [edgeLeft, edgeRight]
  constructor
  · rintro ⟨ha, hn⟩
    refine ⟨?_, hn⟩
    have hne : a.val ≠ e.val := by
      intro hv
      have : a = e := Fin.ext hv
      exact hn (this ▸ he)
    omega
  · rintro ⟨ha, hn⟩
    exact ⟨by omega, hn⟩

theorem componentIndex_edge_missing (G : PathEdges N) (e : Fin (N-1)) (he : e ∉ G) :
    componentIndex G (edgeRight e) = componentIndex G (edgeLeft e) + 1 := by
  have hset : (Finset.univ.filter fun a : Fin (N-1) =>
      a.val < (edgeRight e).val ∧ a ∉ G) =
      insert e (Finset.univ.filter fun a : Fin (N-1) =>
        a.val < (edgeLeft e).val ∧ a ∉ G) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    dsimp [edgeLeft, edgeRight]
    constructor
    · rintro ⟨ha, hn⟩
      by_cases hv : a.val = e.val
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr ⟨by omega, hn⟩
    · rintro (rfl | ⟨ha, hn⟩)
      · exact ⟨by omega, he⟩
      · exact ⟨by omega, hn⟩
  simp only [componentIndex, hset]
  rw [Finset.card_insert_of_notMem]
  simp [edgeLeft]

theorem componentSet_disjoint (G : PathEdges N) {a b : ℕ} (hab : a ≠ b) :
    Disjoint (componentSet G a) (componentSet G b) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hab ((mem_componentSet G a i).mp hi |>.symm.trans ((mem_componentSet G b i).mp hj))

theorem left_right_disjoint (G : PathEdges N) (e : Fin (N-1)) (he : e ∉ G) :
    Disjoint (leftComponent G e) (rightComponent G e) := by
  apply componentSet_disjoint
  have := componentIndex_edge_missing G e he
  omega

theorem boundary_index_strict (G : PathEdges N) {e f : Fin (N-1)}
    (he : e ∉ G) (hef : e < f) :
    componentIndex G (edgeLeft e) < componentIndex G (edgeLeft f) := by
  have hpos : edgeRight e ≤ edgeLeft f := by
    change e.val + 1 ≤ f.val
    exact hef
  have hle := componentIndex_le G hpos
  have hs := componentIndex_edge_missing G e he
  omega

theorem boundarySupport_disjoint_sameParity (G : PathEdges N) {e f : Fin (N-1)}
    (he : e ∉ G) (hf : f ∉ G) (hef : e ≠ f)
    (hp : boundaryParity G e = boundaryParity G f) :
    Disjoint (boundarySupport G e) (boundarySupport G f) := by
  have heq := componentIndex_edge_missing G e he
  have hfq := componentIndex_edge_missing G f hf
  have hne : componentIndex G (edgeLeft e) ≠ componentIndex G (edgeLeft f) := by
    rcases lt_or_gt_of_ne hef with hlt | hgt
    · exact ne_of_lt (boundary_index_strict G he hlt)
    · exact ne_of_gt (boundary_index_strict G hf hgt)
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [boundarySupport, Finset.mem_union, leftComponent, rightComponent,
    mem_componentSet] at hi hj
  dsimp [boundaryParity] at hp
  omega

theorem retainedBoundaries_card_le (G : PathEdges N) (H : Finset (Fin N)) :
    (retainedBoundaries G H).card ≤ H.card := by
  apply (Finset.card_le_card Finset.sdiff_subset).trans
  apply Finset.card_le_card_of_injOn (f := edgeLeft)
  · intro e he
    exact (Finset.mem_filter.mp he).2.1
  · intro e _ f _ hef
    apply Fin.ext
    exact congrArg (fun i : Fin N => i.val) hef

theorem boundaryAscent_congr_relativeOrder (G : PathEdges N) (e : Fin (N-1))
    (π τ : Permutation N)
    (h : ∀ x ∈ boundarySupport G e, ∀ y ∈ boundarySupport G e,
      (π x < π y ↔ τ x < τ y)) :
    boundaryAscent G e π ↔ boundaryAscent G e τ := by
  constructor <;> intro hb x hx y hy
  · exact (h x (Finset.mem_union_left _ hx) y (Finset.mem_union_right _ hy)).mp
      (hb x hx y hy)
  · exact (h x (Finset.mem_union_left _ hx) y (Finset.mem_union_right _ hy)).mpr
      (hb x hx y hy)

theorem leftComponent_le_endpoint (G : PathEdges N) (e : Fin (N-1)) (he : e ∉ G)
    {i : Fin N} (hi : i ∈ leftComponent G e) : i ≤ edgeLeft e := by
  have hc : componentIndex G i = componentIndex G (edgeLeft e) := by
    simpa [leftComponent] using hi
  by_contra hn
  have hr : edgeRight e ≤ i := by
    change e.val + 1 ≤ i.val
    change ¬ i.val ≤ e.val at hn
    omega
  have hle := componentIndex_le G hr
  have hs := componentIndex_edge_missing G e he
  omega

theorem endpoint_le_rightComponent (G : PathEdges N) (e : Fin (N-1)) (he : e ∉ G)
    {i : Fin N} (hi : i ∈ rightComponent G e) : edgeRight e ≤ i := by
  have hc : componentIndex G i = componentIndex G (edgeRight e) := by
    simpa [rightComponent] using hi
  by_contra hn
  have hl : i ≤ edgeLeft e := by
    change i.val ≤ e.val
    change ¬ e.val + 1 ≤ i.val at hn
    omega
  have hle := componentIndex_le G hl
  have hs := componentIndex_edge_missing G e he
  omega

theorem sorted_left_endpoint_ge (G : PathEdges N) (e : Fin (N-1)) (he : e ∉ G)
    (π : Permutation N) {x : Fin N} (hx : x ∈ leftComponent G e) :
    π x ≤ componentSort G π (edgeLeft e) := by
  let i := (componentSort G π).symm (π x)
  have hi : i ∈ leftComponent G e := by
    have hpres := Model.componentSort_preserves_component G π i
    have hval : componentSort G π i = π x := Equiv.apply_symm_apply _ _
    rw [hval, π.symm_apply_apply] at hpres
    simpa [leftComponent, hpres] using hx
  have hle := leftComponent_le_endpoint G e he hi
  have heq : componentIndex G i = componentIndex G (edgeLeft e) := by
    simpa [leftComponent] using hi
  rcases hle.eq_or_lt with h | h
  · have hval : componentSort G π i = π x := Equiv.apply_symm_apply _ _
    rw [← hval, h]
  · have hs := Model.componentSort_increasing G π h heq
    have hval : componentSort G π i = π x := Equiv.apply_symm_apply _ _
    exact (hval ▸ hs).le

theorem sorted_right_endpoint_le (G : PathEdges N) (e : Fin (N-1)) (he : e ∉ G)
    (π : Permutation N) {y : Fin N} (hy : y ∈ rightComponent G e) :
    componentSort G π (edgeRight e) ≤ π y := by
  let i := (componentSort G π).symm (π y)
  have hi : i ∈ rightComponent G e := by
    have hpres := Model.componentSort_preserves_component G π i
    have hval : componentSort G π i = π y := Equiv.apply_symm_apply _ _
    rw [hval, π.symm_apply_apply] at hpres
    simpa [rightComponent, hpres] using hy
  have hle := endpoint_le_rightComponent G e he hi
  have heq : componentIndex G i = componentIndex G (edgeRight e) := by
    simpa [rightComponent] using hi
  rcases hle.eq_or_lt with h | h
  · have hval : componentSort G π i = π y := Equiv.apply_symm_apply _ _
    rw [← hval, h]
  · have hs := Model.componentSort_increasing G π h heq.symm
    have hval : componentSort G π i = π y := Equiv.apply_symm_apply _ _
    exact (hval ▸ hs).le

theorem componentSort_boundary_ascent_iff (G : PathEdges N) (e : Fin (N-1))
    (he : e ∉ G) (π : Permutation N) :
    componentSort G π (edgeLeft e) < componentSort G π (edgeRight e) ↔
      boundaryAscent G e π := by
  constructor
  · intro h x hx y hy
    exact lt_of_le_of_lt (sorted_left_endpoint_ge G e he π hx)
      (lt_of_lt_of_le h (sorted_right_endpoint_le G e he π hy))
  · intro h
    have hx : π.symm (componentSort G π (edgeLeft e)) ∈ leftComponent G e := by
      simpa [leftComponent] using Model.componentSort_preserves_component G π (edgeLeft e)
    have hy : π.symm (componentSort G π (edgeRight e)) ∈ rightComponent G e := by
      simpa [rightComponent] using Model.componentSort_preserves_component G π (edgeRight e)
    simpa using h _ hx _ hy

theorem componentSort_internal_ascent (G : PathEdges N) (e : Fin (N-1))
    (he : e ∈ G) (π : Permutation N) :
    componentSort G π (edgeLeft e) < componentSort G π (edgeRight e) := by
  exact Model.componentSort_increasing G π (by simp [edgeLeft, edgeRight])
    (componentIndex_edge_present G e he).symm

theorem component_ascent_decomposition (G : PathEdges N) (H : Finset (Fin N))
    (π : Permutation N) :
    ascentCount H (componentSort G π) = (G ∩ internalEdges H).card +
      ∑ e ∈ retainedBoundaries G H, if boundaryAscent G e π then 1 else 0 := by
  have hset : (internalEdges H).filter
      (fun e => componentSort G π (edgeLeft e) < componentSort G π (edgeRight e)) =
      (G ∩ internalEdges H) ∪ (retainedBoundaries G H).filter (fun e => boundaryAscent G e π) := by
    ext e
    by_cases he : e ∈ G
    · simp [he, componentSort_internal_ascent G e he π]
    · simp [he, componentSort_boundary_ascent_iff G e he π]
  have hd : Disjoint (G ∩ internalEdges H)
      ((retainedBoundaries G H).filter (fun e => boundaryAscent G e π)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (mem_retainedBoundaries G H e).mp (Finset.mem_filter.mp hf).1 |>.2
      (Finset.mem_inter.mp he).1
  unfold ascentCount
  rw [hset, Finset.card_union_of_disjoint hd]
  congr 1
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem componentIndex_empty_injective : Function.Injective (componentIndex (∅ : PathEdges N)) := by
  intro i j hij
  by_contra hne
  suffices hlt : ∀ a b : Fin N, a < b →
      componentIndex (∅ : PathEdges N) a < componentIndex (∅ : PathEdges N) b by
    rcases lt_or_gt_of_ne hne with h | h
    · exact (ne_of_lt (hlt i j h)) hij
    · exact (ne_of_gt (hlt j i h)) hij
  intro a b hab
  let e : Fin (N-1) := ⟨a.val, by have := b.isLt; omega⟩
  have he : edgeLeft e = a := by apply Fin.ext; rfl
  have hb : edgeRight e ≤ b := by change a.val+1 ≤ b.val; exact hab
  have hs := componentIndex_edge_missing (∅ : PathEdges N) e (Finset.notMem_empty _)
  have hl := componentIndex_le (∅ : PathEdges N) hb
  rw [he] at hs
  omega

@[simp] theorem componentSort_empty (π : Permutation N) : componentSort ∅ π = π := by
  apply Equiv.ext
  intro i
  have h := componentIndex_empty_injective (Model.componentSort_preserves_component ∅ π i)
  simpa using congrArg π h

end RiffleLowerV2.Ascent
