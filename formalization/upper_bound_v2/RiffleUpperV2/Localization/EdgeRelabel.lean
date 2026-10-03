import RiffleUpperV2.Localization.Edges

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Localization
open Anchor

/-- Push row labels forward by σ; values are pulled back by σ⁻¹. -/
def relabelHistory {k n d : ℕ} (σ : Permutation n) (u : InternalHistory k n d) : InternalHistory k n d :=
  fun r => u (σ.symm r)

private theorem filter_map_relabel {n : ℕ} (σ : Permutation n) (R : Finset (Fin n))
    (P : Fin n → Prop) :
    (R.map σ.toEmbedding).filter (fun r => P (σ.symm r)) = (R.filter P).map σ.toEmbedding := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨⟨q,hq,rfl⟩,hP⟩
    exact ⟨q,⟨hq,by simpa using hP⟩,rfl⟩
  · rintro ⟨q,⟨hq,hP⟩,rfl⟩
    exact ⟨⟨q,hq,rfl⟩,by simpa using hP⟩

theorem prefixRows_relabel {k n d : ℕ} (cuts : Cuts k n d) (σ : Permutation n)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    Anchor.prefixRows (R.map σ.toEmbedding) x (RiffleLowerV2.Model.sampleRelabel cuts σ.symm ω) =
      (Anchor.prefixRows R x ω).map σ.toEmbedding := by
  unfold Anchor.prefixRows
  simp only [RiffleLowerV2.Model.rowWord_relabel]
  simpa only [RiffleUpperV2.rowWord] using filter_map_relabel σ R
    (fun r => (rowWord ω r).toList.take x.1.val = x.2.toList)

theorem lowerEndpoint_relabel {k n d : ℕ} (cuts : Cuts k n d) (σ : Permutation n)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    lowerEndpoint c₀ (R.map σ.toEmbedding) x (RiffleLowerV2.Model.sampleRelabel cuts σ.symm ω) =
      lowerEndpoint c₀ R x ω := by
  unfold lowerEndpoint
  simp only [RiffleLowerV2.Model.rowWord_relabel]
  have h := filter_map_relabel σ R
    (fun r => (RiffleLowerV2.rowWord ω r).toList.take x.1.val < x.2.toList)
  have hc := congrArg Finset.card h
  rw [Finset.card_map] at hc
  congr 1
  congr 1
  convert hc using 1 <;> congr 1 <;> ext r <;> simp

theorem internalHistory_relabel {k n d : ℕ} (cuts : Cuts k n d) (σ : Permutation n)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    internalHistory (R.map σ.toEmbedding) x (RiffleLowerV2.Model.sampleRelabel cuts σ.symm ω) =
      relabelHistory σ (internalHistory R x ω) := by
  funext r
  unfold internalHistory relabelHistory
  rw [prefixRows_relabel]
  have hm : r ∈ (Anchor.prefixRows R x ω).map σ.toEmbedding ↔ σ.symm r ∈ Anchor.prefixRows R x ω := by
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨q,hq,rfl⟩
      simpa using hq
    · intro h
      exact ⟨σ.symm r,h,σ.apply_symm_apply r⟩
  simp only [hm]
  split_ifs
  · rfl
  · rfl

theorem history_counts_relabel {k n d : ℕ} (σ : Permutation n) (u : InternalHistory k n d)
    (w : Fin d → Fin k) :
    (historyWordRows (relabelHistory σ u) w).card = (historyWordRows u w).card ∧
    (historyLessRows (relabelHistory σ u) w).card = (historyLessRows u w).card := by
  constructor
  · unfold historyWordRows relabelHistory
    convert RiffleLowerV2.Model.card_filter_reindex σ.symm (fun r => u r = some w) using 1
      <;> congr 1 <;> ext r <;> simp
  · unfold historyLessRows relabelHistory
    convert RiffleLowerV2.Model.card_filter_reindex σ.symm
      (fun r => ∃ q : Fin d → Fin k, u r = some q ∧ List.ofFn q < List.ofFn w) using 1
      <;> congr 1 <;> ext r <;> simp

theorem internalOffsets_relabel {k n d : ℕ} (σ : Permutation n) (u : InternalHistory k n d) :
    internalOffsets (relabelHistory σ u) = internalOffsets u := by
  unfold internalOffsets
  congr 1
  funext w
  rw [(history_counts_relabel σ u w).1,(history_counts_relabel σ u w).2]

theorem anchoredEdges_relabel {k n d : ℕ} (cuts : Cuts k n d) (σ : Permutation n)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    anchoredEdges c₀ (R.map σ.toEmbedding) x (RiffleLowerV2.Model.sampleRelabel cuts σ.symm ω) =
      anchoredEdges c₀ R x ω := by
  unfold anchoredEdges
  rw [internalHistory_relabel, internalOffsets_relabel, lowerEndpoint_relabel]

end RiffleUpperV2.Localization
