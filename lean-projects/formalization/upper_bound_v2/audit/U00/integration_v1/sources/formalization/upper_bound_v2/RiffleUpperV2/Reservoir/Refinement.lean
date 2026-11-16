import RiffleUpperV2.Reservoir.RestrictedPrefix

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

def pileLabels {k n L : ℕ} {cuts : Cuts k n (L+1)} (p : Fin k) (ω : Sample cuts) : Finset (Fin n) :=
  Finset.univ.filter fun r => (rowWord ω r).get 0=p

theorem pileLabels_card {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (ω : Sample cuts) :
    (pileLabels p ω).card=pileSize cuts p := by
  simpa only [pileLabels,RiffleLowerV2.rowWord_get,sampleEntry,pileSize] using (ω 0).property p

def pileEnumeration {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (ω : Sample cuts) :
    Fin (pileSize cuts p) ↪ Fin n :=
  ⟨fun q => ((pileLabels p ω).equivFinOfCardEq (pileLabels_card cuts p ω)).symm q |>.val,
    Subtype.coe_injective.comp (Equiv.injective _)⟩

theorem pileEnumeration_first {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k) (ω : Sample cuts)
    (q : Fin (pileSize cuts p)) : (tupleWords (pileEnumeration cuts p ω) ω q).get 0=p :=
  (Finset.mem_filter.mp (((pileLabels p ω).equivFinOfCardEq (pileLabels_card cuts p ω)).symm q).property).2

def unmarkedIndices {n r : ℕ} (e : Fin r ↪ Fin n) (M : Finset (Fin n)) : Finset (Fin r) :=
  Finset.univ.filter fun q => e q∉M

/-- Auxiliary row information used for disintegration only. The frozen
natural history remains unchanged. -/
def exposedPileView {k n L : ℕ} {cuts : Cuts k n (L+1)} (p : Fin k)
    (M : Finset (Fin n)) (ω : Sample cuts) :
    Finset (Fin n) × (Fin n → Option (Word k (L+1))) :=
  (pileLabels p ω, fun r => if r∈pileLabels p ω ∧ r∉M then some (rowWord ω r) else none)

theorem exposedPileView_eq_iff {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (M : Finset (Fin n)) (e : Fin (pileSize cuts p) ↪ Fin n)
    (ω₀ ω : Sample cuts) (he : ∀ q, (tupleWords e ω₀ q).get 0=p) :
    exposedPileView p M ω=exposedPileView p M ω₀ ↔
      pileBase cuts p e (unmarkedIndices e M) (tupleWords e ω₀) ω := by
  constructor
  · intro hv
    have hp := congrArg Prod.fst hv
    have hwords := congrArg Prod.snd hv
    change pileLabels p ω=pileLabels p ω₀ at hp
    refine ⟨?_,?_⟩
    · intro q
      have hmem : e q∈pileLabels p ω₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he q⟩
      rw [← hp] at hmem
      exact (Finset.mem_filter.mp hmem).2
    · intro q hq
      have hmem : e q∈pileLabels p ω₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he q⟩
      have hnot : e q∉M := (Finset.mem_filter.mp hq).2
      have hh := congrFun hwords (e q)
      simp only [exposedPileView,hp,hmem,hnot,and_self,if_true] at hh
      exact Option.some.inj hh
  · intro hB
    have hp : pileLabels p ω=pileLabels p ω₀ := by
      ext r
      simp only [pileLabels,Finset.mem_filter,Finset.mem_univ,true_and]
      exact (tuplePile_exhausts cuts p e ω hB.1 r).trans (tuplePile_exhausts cuts p e ω₀ he r).symm
    apply Prod.ext hp
    funext r
    change (if r∈pileLabels p ω ∧ r∉M then some (rowWord ω r) else none)=
      (if r∈pileLabels p ω₀ ∧ r∉M then some (rowWord ω₀ r) else none)
    rw [hp]
    split_ifs with hr
    · obtain ⟨q,hq⟩ := (tuplePile_exhausts cuts p e ω₀ he r).mp (Finset.mem_filter.mp hr.1).2
      apply congrArg some
      have hh := hB.2 q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hq]; exact hr.2⟩)
      change rowWord ω (e q)=rowWord ω₀ (e q) at hh
      rwa [hq] at hh
    · rfl

theorem unmarkedIndices_card_compl {n r : ℕ} (e : Fin r ↪ Fin n) (M : Finset (Fin n))
    (hM : ∀ i∈M, ∃ q, e q=i) :
    (Finset.univ \ unmarkedIndices e M).card=M.card := by
  apply Finset.card_bij (fun q _ => e q)
  · intro q hq
    simpa only [unmarkedIndices,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,
      true_and,not_not] using hq
  · intro q _ s _ h
    exact e.injective h
  · intro i hi
    obtain ⟨q,rfl⟩ := hM i hi
    exact ⟨q,by simp [unmarkedIndices,hi],rfl⟩

theorem markedPrefix_reindex {k n L m : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (f : Fin m ↪ Fin n)
    (hf : ∀ i, ∃ q, e q=f i) (E : ℕ) (v : Word k (min E L)) (ω : Sample cuts) :
    (∀ i, tailPrefix E (rowWord ω (f i))=v) ↔
      ∀ q, q∉unmarkedIndices e (Finset.univ.map f) → tailPrefix E (tupleWords e ω q)=v := by
  constructor
  · intro h q hq
    have hmem : e q∈Finset.univ.map f := by simpa [unmarkedIndices] using hq
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hmem
    change tailPrefix E (rowWord ω (e q))=v
    rw [← hi]
    exact h i
  · intro h i
    obtain ⟨q,hq⟩ := hf i
    have hh := h q (by simp [unmarkedIndices,hq])
    change tailPrefix E (rowWord ω (e q))=v at hh
    rwa [hq] at hh

end RiffleUpperV2.Reservoir
