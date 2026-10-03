import RiffleUpperV2.Localization.EdgeCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Localization
open Anchor

theorem historyLess_word_card_le_support {k n d : ℕ} (u : InternalHistory k n d) (w : Fin d → Fin k) :
    (historyLessRows u w).card+(historyWordRows u w).card ≤ (historySupport u).card := by
  rw [← Finset.card_union_of_disjoint (historyLess_disjoint_word u w)]
  apply Finset.card_le_card
  intro r hr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rcases Finset.mem_union.mp hr with h | h
  · obtain ⟨q,hq,_⟩ := (Finset.mem_filter.mp h).2
    simp [hq]
  · have hq := (Finset.mem_filter.mp h).2
    simp [hq]

theorem internalOffsets_bounds_support {k n d : ℕ} (u : InternalHistory k n d) {j : ℤ}
    (hj : j ∈ internalOffsets u) : 0≤j ∧ j<(historySupport u).card-1 := by
  obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hw
  have hc := historyLess_word_card_le_support u w
  have hc' : ((historyLessRows u w).card : ℤ)+(historyWordRows u w).card ≤ (historySupport u).card := by
    exact_mod_cast hc
  have hz : (0:ℤ)≤(historyLessRows u w).card := Int.natCast_nonneg _
  omega

/-- An anchored edge and its right endpoint both lie in the actual prefix interval. -/
theorem anchoredEdges_bounds {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) {m : ℤ}
    (hm : m ∈ anchoredEdges c₀ R x ω) :
    lowerEndpoint c₀ R x ω ≤ m ∧ m+1 < upperEndpoint c₀ R x ω := by
  obtain ⟨j,hj,hjm⟩ := Finset.mem_image.mp hm
  have hb := internalOffsets_bounds_support _ hj
  rw [historySupport_internal] at hb
  unfold upperEndpoint
  omega

theorem anchoredEdges_subset_interval {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    anchoredEdges c₀ R x ω ⊆ anchoredInterval c₀ R x ω := by
  intro m hm
  have h := anchoredEdges_bounds c₀ R x ω hm
  exact Finset.mem_Ico.mpr ⟨h.1,by omega⟩

theorem fullPrefix_rows {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (w : Word k d) (ω : Sample cuts) :
    prefixRows R (RiffleLowerV2.fullPrefix w) ω=R.filter (fun r => rowWord ω r=w) := by
  ext r
  simp only [prefixRows,Finset.mem_filter,RiffleLowerV2.fullPrefix,Fin.val_last]
  apply and_congr_right
  intro _
  rw [List.take_of_length_le (by simp)]
  exact List.Vector.toList_injective.eq_iff

theorem fullPrefix_lower {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (w : Word k d) (ω : Sample cuts) :
    lowerEndpoint c₀ R (RiffleLowerV2.fullPrefix w) ω=c₀+wordLower R w ω := by
  unfold lowerEndpoint wordLower RiffleLowerV2.fullPrefix
  simp only [Fin.val_last,List.take_of_length_le (by simp : (rowWord ω _).toList.length ≤ d)]

theorem wordEdgeInterval_ordered {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (w z : Word k d) (ω : Sample cuts) (hwz : w.toList<z.toList) :
    c₀+wordLower R w ω+restrictedWordCount R w ω ≤ c₀+wordLower R z ω := by
  have h := same_depth_endpoints_ordered c₀ R
    (x := RiffleLowerV2.fullPrefix w) (y := RiffleLowerV2.fullPrefix z) rfl hwz ω
  rw [upperEndpoint,fullPrefix_lower,fullPrefix_lower,fullPrefix_rows] at h
  exact h

theorem wordEdgeInterval_disjoint {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (w z : Word k d) (ω : Sample cuts) (hwz : w≠z) :
    Disjoint (wordEdgeInterval c₀ R w ω) (wordEdgeInterval c₀ R z ω) := by
  apply Finset.disjoint_left.mpr
  intro m hm hn
  obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hm
  obtain ⟨hl',hu'⟩ := Finset.mem_Ico.mp hn
  rcases lt_trichotomy w.toList z.toList with h | h | h
  · have ho := wordEdgeInterval_ordered c₀ R w z ω h
    omega
  · exact hwz (List.Vector.toList_injective h)
  · have ho := wordEdgeInterval_ordered c₀ R z w ω h
    omega

/-- Distinct stable cylinders carry disjoint sets of actual anchored edge ranks. -/
theorem anchoredEdges_stable_disjoint {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (hn : 0<n)
    (c₀ : ℤ) (R : Finset (Fin n)) (v : Prefix k d) (δ : ℝ) (ω : Sample cuts)
    {x y : Prefix k d} (hx : Stable N cuts R v δ x) (hy : Stable N cuts R v δ y) (hne : x≠y) :
    Disjoint (anchoredEdges c₀ R x ω) (anchoredEdges c₀ R y ω) := by
  apply Finset.disjoint_left.mpr
  intro m hmx hmy
  obtain ⟨w,hw,hxw,hmw⟩ := (anchoredEdges_mem_legal_word cuts hn c₀ R x ω m).mp hmx
  obtain ⟨z,hz,hyz,hmz⟩ := (anchoredEdges_mem_legal_word cuts hn c₀ R y ω m).mp hmy
  have hwz : w=z := by
    by_contra h
    exact Finset.disjoint_left.mp (wordEdgeInterval_disjoint c₀ R w z ω h) hmw hmz
  subst z
  rcases List.prefix_or_prefix_of_prefix hxw hyz with h | h
  · exact hne (stable_antichain hx hy h)
  · exact hne (stable_antichain hy hx h).symm

end RiffleUpperV2.Localization
