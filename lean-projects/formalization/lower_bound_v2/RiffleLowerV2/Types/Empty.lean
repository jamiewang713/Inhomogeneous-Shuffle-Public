import RiffleLowerV2.Types.MassBins

noncomputable section
open TimeProfile
namespace RiffleLowerV2.Types
attribute [local instance] Classical.propDecidable

/-- The explicit zero-count, zero-bin data for an empty selected block. -/
def emptyTypeData {k : ℕ} (P : BorelPartition k) : RoundedTypeData P :=
  ⟨fun _ _ => 0, 0⟩

@[simp] lemma massOn_empty {k N K : ℕ} (cuts : Cuts k N K)
    (x : WordOn k (∅ : Finset (Fin K))) : massOn cuts x = 1 := by
  simp [massOn]

@[simp] lemma roundedClass_empty {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) :
    roundedClass cuts hN P (∅ : Finset (Fin K)) (emptyTypeData P) = Finset.univ := by
  ext x
  simp [roundedClass, wordCellCount, emptyTypeData]

@[simp] lemma selectedClass_empty {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) :
    selectedClass cuts hN P (∅ : Finset (Fin K)) (emptyTypeData P) = Finset.univ := by
  ext x
  simp [selectedClass, massBin, emptyTypeData, roundedClass, wordCellCount, massOn]

lemma empty_classes_card_one {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) :
    (roundedClass cuts hN P (∅ : Finset (Fin K)) (emptyTypeData P)).card = 1 ∧
      (selectedClass cuts hN P (∅ : Finset (Fin K)) (emptyTypeData P)).card = 1 := by
  simp [WordOn]

lemma empty_exponents_zero {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) :
    typeJ N (emptyTypeData P) = 0 ∧
      typeH cuts hN P (∅ : Finset (Fin K)) (emptyTypeData P) = 0 := by
  constructor
  · simp [typeJ, emptyTypeData]
  · unfold typeH
    rw [(empty_classes_card_one cuts hN P).2]
    simp

end RiffleLowerV2.Types
