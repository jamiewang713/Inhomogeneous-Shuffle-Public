import RiffleUpperV2.Reservoir.MarkedPrefix
import RiffleUpperV2.Reservoir.HistoryExtension

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile RiffleLowerV2.Thinning
attribute [local instance 2000] wordDecEq

def indexEmbedding {r : ℕ} (A : Finset (Fin r)) : Fin A.card ↪ Fin r :=
  ⟨fun q => (A.equivFin.symm q).val, Subtype.coe_injective.comp A.equivFin.symm.injective⟩

theorem indexEmbedding_mem {r : ℕ} (A : Finset (Fin r)) (q : Fin A.card) :
    indexEmbedding A q ∈ A := (A.equivFin.symm q).property

theorem indexEmbedding_range {r : ℕ} (A : Finset (Fin r)) (q : Fin r) :
    (∃ i, indexEmbedding A i=q) ↔ q∈A := by
  constructor
  · rintro ⟨i,rfl⟩
    exact indexEmbedding_mem A i
  · intro hq
    exact ⟨A.equivFin ⟨q,hq⟩, congrArg Subtype.val (A.equivFin.symm_apply_apply _)⟩

def exposedPrescription {k n L r : ℕ} (e : Fin r ↪ Fin n)
    (A : Finset (Fin r)) (a : Fin r → Word k L) : RiffleLowerV2.RowPrescription n k L A.card where
  row := fun q => e (indexEmbedding A q)
  word := fun q => a (indexEmbedding A q)

def markedLabels {n r : ℕ} (e : Fin r ↪ Fin n) (A : Finset (Fin r)) :
    Fin (Finset.univ \ A).card ↪ Fin n := (indexEmbedding (Finset.univ \ A)).trans e

theorem exposedPrescription_injective {k n L r : ℕ} (e : Fin r ↪ Fin n)
    (A : Finset (Fin r)) (a : Fin r → Word k L) :
    Function.Injective (exposedPrescription e A a).row :=
  e.injective.comp (indexEmbedding A).injective

theorem exposedPrescription_event {k n L r : ℕ} {cuts : Cuts k n L}
    (e : Fin r ↪ Fin n) (A : Finset (Fin r)) (a : Fin r → Word k L) (ω : Sample cuts) :
    RiffleLowerV2.prescriptionEvent (exposedPrescription e A a) ω ↔
      ∀ q ∈ A, tupleWords e ω q = a q := by
  constructor
  · intro h q hq
    obtain ⟨i,rfl⟩ := (indexEmbedding_range A q).mpr hq
    exact h i
  · intro h i
    exact h _ (indexEmbedding_mem A i)

theorem exposedPrescription_used {k n L r : ℕ} (e : Fin r ↪ Fin n)
    (A : Finset (Fin r)) (a : Fin r → Word k L) (j : Fin L) (d : Fin k) :
    RiffleLowerV2.usedCount (exposedPrescription e A a) j d = selectedDigitCount A a j d := by
  apply Finset.card_bij (fun q _ => indexEmbedding A q)
  · intro q hq
    exact Finset.mem_filter.mpr ⟨indexEmbedding_mem A q, (Finset.mem_filter.mp hq).2⟩
  · intro q _ s _ h
    exact (indexEmbedding A).injective h
  · intro q hq
    obtain ⟨i,rfl⟩ := (indexEmbedding_range A q).mpr (Finset.mem_filter.mp hq).1
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩, rfl⟩

theorem markedLabels_disjoint {k n L r : ℕ} (e : Fin r ↪ Fin n)
    (A : Finset (Fin r)) (a : Fin r → Word k L) :
    ∀ i q, (exposedPrescription e A a).row i ≠ markedLabels e A q := by
  intro i q h
  have he := e.injective h
  have hm := indexEmbedding_mem A i
  rw [he] at hm
  exact (Finset.mem_sdiff.mp (indexEmbedding_mem (Finset.univ \ A) q)).2 hm

theorem markedLabels_range {n r : ℕ} (e : Fin r ↪ Fin n)
    (A : Finset (Fin r)) (q : Fin r) :
    (∃ i, markedLabels e A i=e q) ↔ q∉A := by
  constructor
  · rintro ⟨i,hi⟩
    have h := e.injective hi
    have hm := indexEmbedding_mem (Finset.univ \ A) i
    rw [h] at hm
    exact (Finset.mem_sdiff.mp hm).2
  · intro hq
    obtain ⟨i,hi⟩ := (indexEmbedding_range (Finset.univ \ A) q).mpr (by simp [hq])
    exact ⟨i, congrArg e hi⟩

theorem exposedPrescription_probability_pos {k n L r : ℕ} (cuts : Cuts k n L)
    (e : Fin r ↪ Fin n) (A : Finset (Fin r)) (a : Fin r → Word k L)
    (ω : Sample cuts) (h : ∀ q ∈ A, tupleWords e ω q = a q) :
    0 < probability (fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent (exposedPrescription e A a)) := by
  have hh := tupleWords_event_positive cuts e (fun w => ∀ q∈A, w q=a q) ω h
  rw [← tupleWords_event] at hh
  have he : (fun ω : Sample cuts => ∀ q∈A, tupleWords e ω q=a q) =
      RiffleLowerV2.prescriptionEvent (exposedPrescription e A a) := by
    funext ω
    exact propext (exposedPrescription_event e A a ω).symm
  rwa [he] at hh

end RiffleUpperV2.Reservoir
