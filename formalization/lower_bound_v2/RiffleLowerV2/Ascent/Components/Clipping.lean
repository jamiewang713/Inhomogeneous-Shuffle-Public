import RiffleLowerV2.Ascent.Components

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Ascent

variable {N : ℕ}

def crossingEdges (G : PathEdges N) (H : Finset (Fin N)) : PathEdges N :=
  G.filter fun e => ¬ (edgeLeft e ∈ H ↔ edgeRight e ∈ H)

def partialComponents (G : PathEdges N) (H : Finset (Fin N)) : Finset ℕ :=
  (H.image (componentIndex G)).filter fun j => ¬ componentSet G j ⊆ H

def badLeftBoundaries (G : PathEdges N) (H : Finset (Fin N)) : PathEdges N :=
  (retainedBoundaries G H).filter fun e => ¬ leftComponent G e ⊆ H

def badRightBoundaries (G : PathEdges N) (H : Finset (Fin N)) : PathEdges N :=
  (retainedBoundaries G H).filter fun e => ¬ rightComponent G e ⊆ H

def badBoundaries (G : PathEdges N) (H : Finset (Fin N)) : PathEdges N :=
  badLeftBoundaries G H ∪ badRightBoundaries G H

def goodBoundaries (G : PathEdges N) (H : Finset (Fin N)) : PathEdges N :=
  retainedBoundaries G H \ badBoundaries G H

theorem componentIndex_eq_between (G : PathEdges N) {i j k : Fin N}
    (hij : i ≤ j) (hjk : j ≤ k) (hik : componentIndex G i = componentIndex G k) :
    componentIndex G j = componentIndex G i := by
  have h₁ := componentIndex_le G hij
  have h₂ := componentIndex_le G hjk
  omega

theorem edge_mem_of_same_component (G : PathEdges N) {i j : Fin N}
    (e : Fin (N-1)) (hi : i ≤ edgeLeft e) (hj : edgeRight e ≤ j)
    (hij : componentIndex G i = componentIndex G j) : e ∈ G := by
  by_contra he
  have hl := componentIndex_le G hi
  have hr := componentIndex_le G hj
  have hs := componentIndex_edge_missing G e he
  omega

theorem exists_crossing_of_same_component (G : PathEdges N) (H : Finset (Fin N))
    {i j : Fin N} (hc : componentIndex G i = componentIndex G j)
    (hH : ¬ (i ∈ H ↔ j ∈ H)) :
    ∃ e ∈ crossingEdges G H, componentIndex G (edgeLeft e) = componentIndex G i := by
  suffices forward : ∀ a b : Fin N, a ≤ b → componentIndex G a = componentIndex G b →
      ¬ (a ∈ H ↔ b ∈ H) →
      ∃ e ∈ crossingEdges G H, componentIndex G (edgeLeft e) = componentIndex G a by
    rcases le_total i j with hij | hji
    · exact forward i j hij hc hH
    · obtain ⟨e, he, hec⟩ := forward j i hji hc.symm (fun h => hH h.symm)
      exact ⟨e, he, hec.trans hc.symm⟩
  intro a b hab hc hH
  generalize hd : b.val - a.val = d
  induction d generalizing a b with
  | zero =>
      have : a = b := Fin.ext (by omega)
      exact (hH (by simp [this])).elim
  | succ d ih =>
      let e : Fin (N-1) := ⟨a.val, by have := b.isLt; omega⟩
      have hel : edgeLeft e = a := by apply Fin.ext; rfl
      have heb : edgeRight e ≤ b := by change a.val+1 ≤ b.val; omega
      have heG : e ∈ G := edge_mem_of_same_component G e (by rw [hel]) heb hc
      have her : componentIndex G (edgeRight e) = componentIndex G a := by
        rw [componentIndex_edge_present G e heG, hel]
      by_cases hstep : a ∈ H ↔ edgeRight e ∈ H
      · have hd' : b.val - (edgeRight e).val = d := by
          change b.val - (a.val+1) = d
          omega
        obtain ⟨f, hf, hfc⟩ := ih (edgeRight e) b heb (her.trans hc)
          (fun h => hH (hstep.trans h)) hd'
        exact ⟨f, hf, hfc.trans her⟩
      · refine ⟨e, ?_, by rw [hel]⟩
        simp [crossingEdges, heG, hel, hstep]

theorem partialComponents_subset_crossingImage (G : PathEdges N) (H : Finset (Fin N)) :
    partialComponents G H ⊆
      (crossingEdges G H).image (fun e => componentIndex G (edgeLeft e)) := by
  intro j hj
  obtain ⟨himg, hnot⟩ := Finset.mem_filter.mp hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp himg
  obtain ⟨k, hk, hkH⟩ := Finset.not_subset.mp hnot
  have hki : componentIndex G k = componentIndex G i := (mem_componentSet _ _ _).mp hk
  obtain ⟨e, he, hec⟩ := exists_crossing_of_same_component G H hki.symm
    (by simp [hi, hkH])
  exact Finset.mem_image.mpr ⟨e, he, hec⟩

theorem crossingEdges_card_le_boundary (G : PathEdges N) (H : Finset (Fin N)) :
    (crossingEdges G H).card ≤ (boundary H).card := by
  apply Finset.card_le_card_of_injOn (f := fun e => manuscriptRank (edgeLeft e))
  · intro e he
    have hx := (Finset.mem_filter.mp he).2
    have hl : manuscriptRank (edgeLeft e) ∈ rankSet H ↔ edgeLeft e ∈ H := by
      simp only [rankSet, Finset.mem_image]
      constructor
      · rintro ⟨i, hi, hv⟩
        have : i = edgeLeft e := by
          apply Fin.ext
          dsimp [manuscriptRank] at hv
          omega
        exact this ▸ hi
      · intro hi
        exact ⟨_, hi, rfl⟩
    have hr : manuscriptRank (edgeLeft e) + 1 ∈ rankSet H ↔ edgeRight e ∈ H := by
      simp only [rankSet, Finset.mem_image]
      constructor
      · rintro ⟨i, hi, hv⟩
        have : i = edgeRight e := by apply Fin.ext; dsimp [manuscriptRank, edgeLeft, edgeRight] at hv ⊢; omega
        exact this ▸ hi
      · intro hi
        exact ⟨edgeRight e, hi, by dsimp [manuscriptRank, edgeLeft, edgeRight]⟩
    change manuscriptRank (edgeLeft e) ∈ boundary H
    simp only [boundary, integerBoundary, Finset.mem_filter, Finset.mem_union]
    constructor
    · by_cases hh : edgeLeft e ∈ H
      · exact Or.inl (hl.mpr hh)
      · apply Or.inr
        have hright : edgeRight e ∈ H := by tauto
        exact Finset.mem_image.mpr
          ⟨manuscriptRank (edgeLeft e)+1, hr.mpr hright, by omega⟩
    · rw [hl, hr]
      tauto
  · intro e _ f _ hef
    apply Fin.ext
    dsimp [manuscriptRank, edgeLeft] at hef
    omega

theorem partialComponents_card_le_boundary (G : PathEdges N) (H : Finset (Fin N)) :
    (partialComponents G H).card ≤ (boundary H).card := by
  exact (Finset.card_le_card (partialComponents_subset_crossingImage G H)).trans
    ((Finset.card_image_le).trans (crossingEdges_card_le_boundary G H))

theorem boundary_left_index_injective (G : PathEdges N) :
    Set.InjOn (fun e : Fin (N-1) => componentIndex G (edgeLeft e)) {e | e ∉ G} := by
  intro e he f hf h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (ne_of_lt (boundary_index_strict G he hlt)) h
  · exact (ne_of_gt (boundary_index_strict G hf hgt)) h

theorem boundary_right_index_injective (G : PathEdges N) :
    Set.InjOn (fun e : Fin (N-1) => componentIndex G (edgeRight e)) {e | e ∉ G} := by
  intro e he f hf h
  apply boundary_left_index_injective G he hf
  dsimp only at h ⊢
  rw [componentIndex_edge_missing G e he, componentIndex_edge_missing G f hf] at h
  omega

theorem badLeftBoundaries_card_le_partial (G : PathEdges N) (H : Finset (Fin N)) :
    (badLeftBoundaries G H).card ≤ (partialComponents G H).card := by
  apply Finset.card_le_card_of_injOn (f := fun e => componentIndex G (edgeLeft e))
  · intro e he
    obtain ⟨hb, hn⟩ := Finset.mem_filter.mp he
    obtain ⟨heH, _⟩ := (mem_retainedBoundaries G H e).mp hb
    have hlH : edgeLeft e ∈ H := (Finset.mem_filter.mp heH).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, hlH, rfl⟩, hn⟩
  · intro e he f hf h
    exact boundary_left_index_injective G
      ((mem_retainedBoundaries G H e).mp (Finset.mem_filter.mp he).1).2
      ((mem_retainedBoundaries G H f).mp (Finset.mem_filter.mp hf).1).2 h

theorem badRightBoundaries_card_le_partial (G : PathEdges N) (H : Finset (Fin N)) :
    (badRightBoundaries G H).card ≤ (partialComponents G H).card := by
  apply Finset.card_le_card_of_injOn (f := fun e => componentIndex G (edgeRight e))
  · intro e he
    obtain ⟨hb, hn⟩ := Finset.mem_filter.mp he
    obtain ⟨heH, _⟩ := (mem_retainedBoundaries G H e).mp hb
    have hrH : edgeRight e ∈ H := (Finset.mem_filter.mp heH).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, hrH, rfl⟩, hn⟩
  · intro e he f hf h
    exact boundary_right_index_injective G
      ((mem_retainedBoundaries G H e).mp (Finset.mem_filter.mp he).1).2
      ((mem_retainedBoundaries G H f).mp (Finset.mem_filter.mp hf).1).2 h

theorem badBoundaries_card_le (G : PathEdges N) (H : Finset (Fin N)) :
    (badBoundaries G H).card ≤ 2 * (boundary H).card := by
  have hl := badLeftBoundaries_card_le_partial G H
  have hr := badRightBoundaries_card_le_partial G H
  have hp := partialComponents_card_le_boundary G H
  have hu := Finset.card_union_le (badLeftBoundaries G H) (badRightBoundaries G H)
  dsimp [badBoundaries]
  omega

end RiffleLowerV2.Ascent
