import RiffleUpperV2.Reservoir.ExposedRows
import RiffleUpperV2.Reservoir.Counts

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

def pileBase {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1)) (ω : Sample cuts) : Prop :=
  (∀ q, (tupleWords e ω q).get 0 = p) ∧ ∀ q ∈ A, tupleWords e ω q=a q

theorem pileBase_iff {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1))
    (hap : ∀ q ∈ A, (a q).get 0=p) (ω : Sample cuts) :
    pileBase cuts p e A a ω ↔
      RiffleLowerV2.prescriptionEvent (exposedPrescription e A a) ω ∧
      ∀ q, sampleEntry ω (markedLabels e A q) 0=p := by
  rw [exposedPrescription_event]
  constructor
  · rintro ⟨hfirst,hfix⟩
    exact ⟨hfix, fun q => hfirst (indexEmbedding (Finset.univ \ A) q)⟩
  · rintro ⟨hfix, hfirst⟩
    refine ⟨?_, hfix⟩
    intro q
    by_cases hq : q∈A
    · rw [hfix q hq]
      exact hap q hq
    · obtain ⟨i,hi⟩ := (markedLabels_range e A q).mpr hq
      have hh := hfirst i
      rwa [hi] at hh

theorem markedTailPrefix_iff {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (A : Finset (Fin (pileSize cuts p)))
    (D : ℕ) (v : Word k (min D L)) (ω : Sample cuts) :
    (∀ i, tailPrefix D (rowWord ω (markedLabels e A i))=v) ↔
      ∀ q, q∉A → tailPrefix D (tupleWords e ω q)=v := by
  constructor
  · intro h q hq
    obtain ⟨i,hi⟩ := (markedLabels_range e A q).mpr hq
    have hh := h i
    rwa [hi] at hh
  · intro h i
    exact h _ (Finset.mem_sdiff.mp (indexEmbedding_mem (Finset.univ \ A) i)).2

/-- The exact source prefix weight under the labeled-pile/unmarked-row
refinement, with the c+m denominator and every exposed digit subtracted. -/
theorem pileBase_tailPrefix_probability {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1))
    (ω₀ : Sample cuts) (ha : ∀ q∈A, tupleWords e ω₀ q=a q)
    (hap : ∀ q∈A, (a q).get 0=p) (D : ℕ) (v : Word k (min D L)) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => ∀ q, q∉A → tailPrefix D (tupleWords e ω q)=v)
      (pileBase cuts p e A a) =
    ∏ j : Fin (min D L), RiffleLowerV2.falling
      (cuts.count ⟨j.val+1, by have := j.isLt; omega⟩ (v.get j) -
        selectedDigitCount A a ⟨j.val+1, by have := j.isLt; omega⟩ (v.get j)) (Finset.univ \ A).card /
      RiffleLowerV2.falling ((n-pileSize cuts p)+(Finset.univ \ A).card) (Finset.univ \ A).card := by
  have hc : (Finset.univ \ A).card ≤ cuts.count 0 p - RiffleLowerV2.usedCount (exposedPrescription e A a) 0 p := by
    rw [exposedPrescription_used, selectedDigitCount_first A a p hap p]
    simp only [if_true, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin]
    exact le_rfl
  have hh := residual_tailPrefixWeight_marked cuts (exposedPrescription e A a)
    (exposedPrescription_injective e A a) (exposedPrescription_probability_pos cuts e A a ω₀ ha)
    (markedLabels e A) (markedLabels_disjoint e A a) D v p hc
  have hB : pileBase cuts p e A a = (fun ω =>
      RiffleLowerV2.prescriptionEvent (exposedPrescription e A a) ω ∧
      ∀ q, sampleEntry ω (markedLabels e A q) 0=p) := by
    funext ω
    exact propext (pileBase_iff cuts p e A a hap ω)
  have hE : (fun ω : Sample cuts => ∀ q, q∉A → tailPrefix D (tupleWords e ω q)=v) =
      (fun ω => ∀ i, tailPrefix D (rowWord ω (markedLabels e A i))=v) := by
    funext ω
    exact propext (markedTailPrefix_iff cuts p e A D v ω).symm
  rw [hB, hE]
  simpa only [exposedPrescription_used, remainingPopulation_eq cuts p A] using hh

/-- Residual capacities are precisely outside-pile rows plus the marked
labels. This connects the exact factorial formula to literal H. -/
theorem residualCount_eq_remaining {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1)) (ω : Sample cuts)
    (hB : pileBase cuts p e A a ω) (j : Fin (L+1)) (d : Fin k) :
    cuts.count j d - selectedDigitCount A a j d =
      remainingCount p ((Finset.univ \ A).map e) j d ω := by
  let U := Finset.univ.filter (fun r : Fin n => (rowWord ω r).get j=d)
  let V := (A.filter fun q => (a q).get j=d).map e
  have hV : V ⊆ U := by
    intro r hr
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hr
    have hqa := (Finset.mem_filter.mp hq).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      change (tupleWords e ω q).get j=d
      rw [hB.2 q hqa]
      exact (Finset.mem_filter.mp hq).2⟩
  have hU : U.card=cuts.count j d := by
    simpa only [U, RiffleLowerV2.rowWord_get, sampleEntry] using (ω j).property d
  have hrem : Finset.univ.filter (fun r : Fin n =>
      ((rowWord ω r).get 0≠p ∨ r∈(Finset.univ \ A).map e) ∧
      (rowWord ω r).get j=d) = U \ V := by
    ext r
    simp only [U,V,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_map]
    constructor
    · rintro ⟨hr,hd⟩
      refine ⟨hd,?_⟩
      rintro ⟨q,⟨hq,hqd⟩,he⟩
      rcases hr with hp | ⟨s,hs,hes⟩
      · have hh := hB.1 q
        change (rowWord ω (e q)).get 0=p at hh
        rw [he] at hh
        exact hp hh
      · exact hs ((e.injective (hes.trans he.symm)) ▸ hq)
    · rintro ⟨hd,hnot⟩
      refine ⟨?_,hd⟩
      by_cases hp : (rowWord ω r).get 0=p
      · obtain ⟨q,he⟩ := (tuplePile_exhausts cuts p e ω hB.1 r).mp hp
        right
        refine ⟨q,?_,he⟩
        intro hq
        apply hnot
        refine ⟨q,⟨hq,?_⟩,he⟩
        rw [← hB.2 q hq]
        change (rowWord ω (e q)).get j=d
        rwa [he]
      · exact Or.inl hp
  unfold remainingCount
  rw [hrem,Finset.card_sdiff_of_subset hV,hU]
  simp only [V,Finset.card_map,selectedDigitCount]

end RiffleUpperV2.Reservoir
