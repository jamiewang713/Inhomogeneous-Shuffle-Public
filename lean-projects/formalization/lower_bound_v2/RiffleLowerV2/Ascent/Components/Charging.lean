import RiffleLowerV2.Ascent.Components.Clipping

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Ascent

variable {N : ℕ}

def componentEdges (G : PathEdges N) (j : ℕ) : PathEdges N :=
  G.filter fun e => componentIndex G (edgeLeft e) = j

@[simp] theorem mem_componentEdges (G : PathEdges N) (j : ℕ) (e : Fin (N-1)) :
    e ∈ componentEdges G j ↔ e ∈ G ∧ componentIndex G (edgeLeft e) = j := by
  simp [componentEdges]

theorem componentEdges_endpoints (G : PathEdges N) (j : ℕ) (e : Fin (N-1))
    (he : e ∈ componentEdges G j) :
    edgeLeft e ∈ componentSet G j ∧ edgeRight e ∈ componentSet G j := by
  obtain ⟨heG, hj⟩ := (mem_componentEdges G j e).mp he
  simp only [mem_componentSet]
  exact ⟨hj, (componentIndex_edge_present G e heG).trans hj⟩

theorem componentSet_card (G : PathEdges N) (j : ℕ) (hj : (componentSet G j).Nonempty) :
    (componentSet G j).card = (componentEdges G j).card + 1 := by
  let m := (componentSet G j).max' hj
  have hm : m ∈ componentSet G j := Finset.max'_mem _ _
  have hmj : componentIndex G m = j := (mem_componentSet _ _ _).mp hm
  have hcard : (componentEdges G j).card = ((componentSet G j).erase m).card := by
    apply Finset.card_bij (fun e _ => edgeLeft e)
    · intro e he
      obtain ⟨hl, hr⟩ := componentEdges_endpoints G j e he
      apply Finset.mem_erase.mpr
      refine ⟨?_, hl⟩
      have hmax : edgeRight e ≤ m := Finset.le_max' _ _ hr
      intro heq
      have hlt : edgeLeft e < edgeRight e := by simp [edgeLeft, edgeRight]
      rw [heq] at hlt
      exact (not_lt_of_ge hmax) hlt
    · intro e _ f _ hef
      apply Fin.ext
      exact congrArg (fun i : Fin N => i.val) hef
    · intro i hi
      obtain ⟨him, hij⟩ := Finset.mem_erase.mp hi
      have hil : i ≤ m := Finset.le_max' _ _ hij
      have himlt : i < m := lt_of_le_of_ne hil him
      let e : Fin (N-1) := ⟨i.val, by have := m.isLt; omega⟩
      have hei : edgeLeft e = i := by apply Fin.ext; rfl
      have her : edgeRight e ≤ m := by change i.val+1 ≤ m.val; exact himlt
      have hij' : componentIndex G i = j := (mem_componentSet _ _ _).mp hij
      have heG : e ∈ G := edge_mem_of_same_component G e (by rw [hei]) her
        (hij'.trans hmj.symm)
      refine ⟨e, (mem_componentEdges _ _ _).mpr ⟨heG, ?_⟩, hei⟩
      rw [hei, hij']
  rw [Finset.card_erase_of_mem hm] at hcard
  have hpos : 0 < (componentSet G j).card := Finset.card_pos.mpr hj
  omega

theorem componentEdges_disjoint (G : PathEdges N) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (componentEdges G i) (componentEdges G j) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact hij (((mem_componentEdges _ _ _).mp he).2.symm.trans
    ((mem_componentEdges _ _ _).mp hf).2)

theorem componentEdges_subset_retainedInternal (G : PathEdges N) (H : Finset (Fin N))
    (j : ℕ) (hfull : componentSet G j ⊆ H) : componentEdges G j ⊆ G ∩ internalEdges H := by
  intro e he
  obtain ⟨hl, hr⟩ := componentEdges_endpoints G j e he
  exact Finset.mem_inter.mpr ⟨((mem_componentEdges _ _ _).mp he).1,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfull hl, hfull hr⟩⟩

@[simp] theorem mem_goodBoundaries (G : PathEdges N) (H : Finset (Fin N)) (e : Fin (N-1)) :
    e ∈ goodBoundaries G H ↔
      e ∈ retainedBoundaries G H ∧ leftComponent G e ⊆ H ∧ rightComponent G e ⊆ H := by
  simp only [goodBoundaries, badBoundaries, badLeftBoundaries, badRightBoundaries,
    Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
  tauto

theorem good_left_charge_le (G : PathEdges N) (H : Finset (Fin N)) :
    (∑ e ∈ goodBoundaries G H, (componentEdges G (componentIndex G (edgeLeft e))).card) ≤
      (G ∩ internalEdges H).card := by
  have hdis : (goodBoundaries G H : Set (Fin (N-1))).PairwiseDisjoint
      (fun e => componentEdges G (componentIndex G (edgeLeft e))) := by
    intro e he f hf hef
    apply componentEdges_disjoint
    intro hij
    have he' := ((mem_retainedBoundaries G H e).mp ((mem_goodBoundaries G H e).mp he).1).2
    have hf' := ((mem_retainedBoundaries G H f).mp ((mem_goodBoundaries G H f).mp hf).1).2
    exact hef (boundary_left_index_injective G he' hf' hij)
  rw [← Finset.card_biUnion hdis]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.mp ha
  exact componentEdges_subset_retainedInternal G H _
    ((mem_goodBoundaries G H e).mp he).2.1 hae

theorem good_right_charge_le (G : PathEdges N) (H : Finset (Fin N)) :
    (∑ e ∈ goodBoundaries G H, (componentEdges G (componentIndex G (edgeRight e))).card) ≤
      (G ∩ internalEdges H).card := by
  have hdis : (goodBoundaries G H : Set (Fin (N-1))).PairwiseDisjoint
      (fun e => componentEdges G (componentIndex G (edgeRight e))) := by
    intro e he f hf hef
    apply componentEdges_disjoint
    intro hij
    have he' := ((mem_retainedBoundaries G H e).mp ((mem_goodBoundaries G H e).mp he).1).2
    have hf' := ((mem_retainedBoundaries G H f).mp ((mem_goodBoundaries G H f).mp hf).1).2
    exact hef (boundary_right_index_injective G he' hf' hij)
  rw [← Finset.card_biUnion hdis]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.mp ha
  exact componentEdges_subset_retainedInternal G H _
    ((mem_goodBoundaries G H e).mp he).2.2 hae

theorem good_boundary_double_charge (G : PathEdges N) (H : Finset (Fin N)) :
    (∑ e ∈ goodBoundaries G H,
      ((leftComponent G e).card - 1 + ((rightComponent G e).card - 1))) ≤
      2 * (G ∩ internalEdges H).card := by
  have hleft (e : Fin (N-1)) : (leftComponent G e).card - 1 =
      (componentEdges G (componentIndex G (edgeLeft e))).card := by
    have h := componentSet_card G (componentIndex G (edgeLeft e))
      ⟨edgeLeft e, by simp⟩
    change (componentSet G (componentIndex G (edgeLeft e))).card - 1 = _
    omega
  have hright (e : Fin (N-1)) : (rightComponent G e).card - 1 =
      (componentEdges G (componentIndex G (edgeRight e))).card := by
    have h := componentSet_card G (componentIndex G (edgeRight e))
      ⟨edgeRight e, by simp⟩
    change (componentSet G (componentIndex G (edgeRight e))).card - 1 = _
    omega
  simp_rw [hleft, hright, Finset.sum_add_distrib]
  have hl := good_left_charge_le G H
  have hr := good_right_charge_le G H
  omega

end RiffleLowerV2.Ascent
