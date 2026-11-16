import RiffleUpperV2.Localization.EdgeRanks
import RiffleUpperV2.Localization.Stopping

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

theorem legal_of_prefixRows_nonempty {k n d : ℕ} (cuts : Cuts k n d) (hn : 0<n)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts)
    (h : (prefixRows R x ω).Nonempty) : Legal cuts R x := by
  obtain ⟨r,hr⟩ := h
  obtain ⟨hR,hx⟩ := Finset.mem_filter.mp hr
  have hRpos : 0<R.card := Finset.card_pos.mpr ⟨r,hR⟩
  have he := (RiffleLowerV2.Thinning.prefix_coordinates_iff x ω r).mp hx
  have hp : 0<prefixMass cuts x := by
    apply Finset.prod_pos
    intro j _
    have hd := TimeProfile.sample_entry_count_pos ω r (Fin.castLE (Nat.le_of_lt_succ x.1.isLt) j)
    rw [he j] at hd
    apply div_pos
    · exact_mod_cast hd
    · exact_mod_cast hn
  exact mul_pos (by exact_mod_cast hRpos) hp

theorem wordEdgeInterval_legal {k n d : ℕ} (cuts : Cuts k n d) (hn : 0<n)
    (c₀ : ℤ) (R : Finset (Fin n)) (w : Word k d) (ω : Sample cuts) {m : ℤ}
    (hm : m ∈ wordEdgeInterval c₀ R w ω) : Legal cuts R (RiffleLowerV2.fullPrefix w) := by
  obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hm
  have hc : 0<restrictedWordCount R w ω := by omega
  obtain ⟨r,hr⟩ := Finset.card_pos.mp hc
  apply legal_of_prefixRows_nonempty cuts hn R _ ω
  refine ⟨r,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1,?_⟩⟩
  rw [(Finset.mem_filter.mp hr).2]
  change w.toList.take d=w.toList
  exact List.take_of_length_le (by simp)

theorem matching_isPrefix_full {k d : ℕ} (x : Prefix k d) (w : Word k d) :
    w.toList.take x.1.val=x.2.toList ↔ IsPrefix x (RiffleLowerV2.fullPrefix w) := by
  constructor
  · intro h
    change x.2.toList <+: w.toList
    rw [← h]
    exact List.take_prefix _ _
  · intro h
    change x.2.toList <+: w.toList at h
    obtain ⟨t,ht⟩ := h
    rw [←ht]
    have ht : (x.2.toList++t).take x.2.toList.length=x.2.toList := by simp
    simpa only [List.Vector.toList_length] using ht

/-- Every actual local edge has an actual legal full-word witness. -/
theorem anchoredEdges_mem_legal_word {k n d : ℕ} (cuts : Cuts k n d) (hn : 0<n)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) (m : ℤ) :
    m ∈ anchoredEdges c₀ R x ω ↔ ∃ w : Word k d,
      Legal cuts R (RiffleLowerV2.fullPrefix w) ∧
      IsPrefix x (RiffleLowerV2.fullPrefix w) ∧ m ∈ wordEdgeInterval c₀ R w ω := by
  rw [anchoredEdges_mem_word]
  constructor
  · rintro ⟨w,hw,hm⟩
    exact ⟨w,wordEdgeInterval_legal cuts hn c₀ R w ω hm,(matching_isPrefix_full x w).mp hw,hm⟩
  · rintro ⟨w,_,hw,hm⟩
    exact ⟨w,(matching_isPrefix_full x w).mpr hw,hm⟩

/-- Literal stable graph cover, with fallback words retained until the terminal
margin is applied. The cover is pointwise in the actual future matrix. -/
theorem anchoredEdges_stable_cover {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (hn : 0<n)
    (c₀ : ℤ) (R : Finset (Fin n)) (v : Prefix k d) (δ : ℝ) (ω : Sample cuts) (m : ℤ) :
    m ∈ anchoredEdges c₀ R v ω ↔ ∃ x : Prefix k d,
      Stable N cuts R v δ x ∧ m ∈ anchoredEdges c₀ R x ω := by
  constructor
  · intro hm
    obtain ⟨w,hw,hvw,hmw⟩ := (anchoredEdges_mem_legal_word cuts hn c₀ R v ω m).mp hm
    obtain ⟨x,⟨hx,hxw⟩,_⟩ := stableCover N cuts hn R v δ
      (w := RiffleLowerV2.fullPrefix w) ⟨hw,rfl,hvw⟩
    exact ⟨x,hx,(anchoredEdges_mem_legal_word cuts hn c₀ R x ω m).mpr ⟨w,hw,hxw,hmw⟩⟩
  · rintro ⟨x,hx,hm⟩
    obtain ⟨w,hw,hxw,hmw⟩ := (anchoredEdges_mem_legal_word cuts hn c₀ R x ω m).mp hm
    exact (anchoredEdges_mem_legal_word cuts hn c₀ R v ω m).mpr ⟨w,hw,hx.2.1.trans hxw,hmw⟩

/-- Edges assigned to a prescribed set of full words. -/
def edgesInWords {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ) (R : Finset (Fin n))
    (W : Finset (Word k d)) (ω : Sample cuts) : Finset ℤ := W.biUnion (fun w => wordEdgeInterval c₀ R w ω)

def rowsInWords {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (W : Finset (Word k d)) (ω : Sample cuts) : Finset (Fin n) := R.filter (fun r => rowWord ω r ∈ W)

/-- Discarding words costs at most their actual row count, with no extra factor. -/
theorem edgesInWords_card_le_rows {k n d : ℕ} {cuts : Cuts k n d} (c₀ : ℤ)
    (R : Finset (Fin n)) (W : Finset (Word k d)) (ω : Sample cuts) :
    (edgesInWords c₀ R W ω).card ≤ (rowsInWords R W ω).card := by
  have hu : W.biUnion (fun w => R.filter (fun r => rowWord ω r=w))=rowsInWords R W ω := by
    ext r
    simp only [Finset.mem_biUnion,Finset.mem_filter,rowsInWords]
    constructor
    · rintro ⟨w,hw,hr,heq⟩
      exact ⟨hr,heq ▸ hw⟩
    · rintro ⟨hr,hw⟩
      exact ⟨rowWord ω r,hw,hr,rfl⟩
  have hd : Set.Pairwise (↑W) (fun w z => Disjoint (R.filter (fun r => rowWord ω r=w))
      (R.filter (fun r => rowWord ω r=z))) := by
    intro w hw z hz hwz
    apply Finset.disjoint_left.mpr
    intro r hr hs
    exact hwz ((Finset.mem_filter.mp hr).2.symm.trans (Finset.mem_filter.mp hs).2)
  have hc := Finset.card_biUnion hd
  rw [hu] at hc
  rw [hc]
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro w hw
  rw [wordEdgeInterval,Int.card_Ico]
  unfold restrictedWordCount
  omega

end RiffleUpperV2.Localization
