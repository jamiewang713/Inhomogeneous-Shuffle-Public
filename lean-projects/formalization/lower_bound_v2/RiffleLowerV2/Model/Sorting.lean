import Contracts.v1.AdditionalFinite

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Model
open TimeProfile

/-- Reindexing a finite predicate by a permutation preserves its cardinality. -/
theorem card_filter_reindex {N : ℕ} (σ : Permutation N) (P : Fin N → Prop) :
    (Finset.univ.filter fun i => P (σ i)).card = (Finset.univ.filter P).card := by
  apply Finset.card_bij (fun i _ => σ i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i _ j _ h
    exact σ.injective h
  · intro i hi
    refine ⟨σ.symm i, ?_, by simp⟩
    simpa using hi

/-- Stable sorting increases original labels within every complete-word block. -/
theorem stableTie : Targets.StableTie := by
  intro k N K cuts ω i j hij heq
  exact (Tuple.eq_sort_iff.mp (rfl : stableSort ω = Tuple.sort (rowWord ω))).2 i j hij heq

/-- Exact prefix positions and cardinalities in the shared zero-based convention. -/
theorem prefixRanks : Targets.PrefixRanks := by
  classical
  intro k N K cuts ω w
  let f : Fin N → List (Fin k) := fun i => (rowWord ω i).toList.take w.1.val
  let g : Fin N → List (Fin k) := fun i => (sortedWord ω i).toList.take w.1.val
  have hm : Monotone g := by
    intro i j hij
    exact RiffleShuffle.take_lex_monotone w.1.val (Tuple.monotone_sort (rowWord ω) hij)
  have hl (i : Fin N) : i.val < lowerRank w ω ↔ g i < w.2.toList := by
    have h := Tuple.lt_card_lt_iff_apply_lt_of_monotone (a := w.2.toList) (j := i) hm
    convert h using 2
    unfold lowerRank
    symm
    apply Finset.card_bij (fun j _ => stableSort ω j)
    · intro j hj
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, g, sortedWord] using hj
    · intro j _ m _ hjm
      exact (stableSort ω).injective hjm
    · intro j hj
      refine ⟨(stableSort ω).symm j, ?_, by simp⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, g, sortedWord,
        Equiv.apply_symm_apply] using hj
  have hu (i : Fin N) : i.val < upperRank w ω ↔ g i ≤ w.2.toList := by
    have h := Tuple.lt_card_le_iff_apply_le_of_monotone (a := w.2.toList) (j := i) hm
    convert h using 2
    unfold upperRank
    symm
    apply Finset.card_bij (fun j _ => stableSort ω j)
    · intro j hj
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, g, sortedWord] using hj
    · intro j _ m _ hjm
      exact (stableSort ω).injective hjm
    · intro j hj
      refine ⟨(stableSort ω).symm j, ?_, by simp⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, g, sortedWord,
        Equiv.apply_symm_apply] using hj
  constructor
  · intro i
    change g i = w.2.toList ↔ _
    constructor
    · intro h
      exact ⟨Nat.le_of_not_gt (fun hi => (hl i).mp hi |>.ne h), (hu i).mpr h.le⟩
    · rintro ⟨hlo, hup⟩
      exact le_antisymm ((hu i).mp hup)
        (le_of_not_gt (fun h => Nat.not_lt_of_ge hlo ((hl i).mpr h)))
  · let A := Finset.univ.filter fun i => f i < w.2.toList
    let B := Finset.univ.filter fun i => f i ≤ w.2.toList
    have hab : A ⊆ B := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩
    have he : Finset.univ.filter (fun i => f i = w.2.toList) = B \ A := by
      ext i
      simp only [A, B, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact eq_iff_le_not_lt.trans (by simp only [not_lt])
    have hc := Finset.card_sdiff_of_subset hab
    rw [← he] at hc
    have hB : upperRank w ω = B.card := by
      unfold upperRank
      apply congrArg Finset.card
      ext i
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    have hA : lowerRank w ω = A.card := by
      unfold lowerRank
      apply congrArg Finset.card
      ext i
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    have hC : prefixCount w ω = (Finset.univ.filter fun i => f i = w.2.toList).card := by
      unfold prefixCount
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    rw [hB, hA, hC]
    exact hc.symm

end RiffleLowerV2.Model
