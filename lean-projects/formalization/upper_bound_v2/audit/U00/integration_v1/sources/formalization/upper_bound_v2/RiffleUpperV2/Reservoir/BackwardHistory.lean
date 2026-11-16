import RiffleUpperV2.Reservoir.History
import Mathlib.Data.Fin.Rev

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

def backwardWords {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) : Fin (pileSize cuts p) → Word k (L+1) :=
  fun r => sortedWord ω (pilePosition cuts p .backward r)

theorem backwardWords_eq_rev {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (r : Fin (pileSize cuts p)) :
    backwardWords cuts p ω r = pileWords cuts p ω (Fin.revPerm r) := by
  apply congrArg (sortedWord ω)
  apply Fin.ext
  change pileOffset cuts p + (pileSize cuts p - 1 - r.val) =
    pileOffset cuts p + (pileSize cuts p - (r.val+1))
  omega

theorem backwardWords_antitone {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) : Antitone (backwardWords cuts p ω) := by
  intro r s hrs
  simp only [backwardWords_eq_rev]
  exact pileWords_monotone cuts p ω (Fin.rev_le_rev.mpr hrs)

theorem backwardWords_first {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (r : Fin (pileSize cuts p)) :
    (backwardWords cuts p ω r).get 0 = p := pilePosition_firstDigit cuts p .backward r ω

theorem backwardWords_count {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (u : Word k (L+1)) :
    tupleCount (backwardWords cuts p ω) u = tupleCount (pileWords cuts p ω) u := by
  unfold tupleCount
  simp only [backwardWords_eq_rev]
  convert RiffleLowerV2.Model.card_filter_reindex Fin.revPerm (fun r => pileWords cuts p ω r = u) using 1 <;>
    (congr 1 <;> ext r <;> simp)

/-- Reversal is spatial only: the terminal word is the minimum revealed word,
and every strictly greater word has its exact observed multiplicity. -/
theorem historyAtom_backward {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω v : Sample cuts) (j : Fin (pileSize cuts p)) :
    historyFiber cuts p .backward (j.val+1) ω v ↔
      (∀ u : Word k (L+1), u.get 0 = p → backwardWords cuts p ω j < u →
        wordCount v u = observedCount (backwardWords cuts p ω) (j.val+1) u) ∧
      observedCount (backwardWords cuts p ω) (j.val+1) (backwardWords cuts p ω j) ≤
        wordCount v (backwardWords cuts p ω j) := by
  have hh : historyFiber cuts p .backward (j.val+1) ω v ↔
      ∀ r : Fin (pileSize cuts p), r.val < j.val+1 →
        backwardWords cuts p v r = backwardWords cuts p ω r := by
    constructor
    · intro h r hr
      exact revealed_word_eq cuts p .backward (j.val+1) h r hr
    · intro h
      funext r
      by_cases hr : r.val < j.val+1
      · simp only [naturalHistory, hr, if_true]
        exact congrArg some (h r hr)
      · simp [naturalHistory, hr]
  have hs := @sorted_history_iff (OrderDual (Word k (L+1))) inferInstance inferInstance
    wordDecEq _ (backwardWords cuts p ω) (backwardWords cuts p v)
    (backwardWords_antitone cuts p ω) (backwardWords_antitone cuts p v) j
  refine hh.trans (hs.trans ?_)
  change ((∀ u : Word k (L+1), backwardWords cuts p ω j < u →
    tupleCount (backwardWords cuts p v) u = observedCount (backwardWords cuts p ω) (j.val+1) u) ∧
    observedCount (backwardWords cuts p ω) (j.val+1) (backwardWords cuts p ω j) ≤
      tupleCount (backwardWords cuts p v) (backwardWords cuts p ω j)) ↔ _
  simp only [backwardWords_count]
  rw [pileWords_count cuts p v _ (backwardWords_first cuts p ω j)]
  apply and_congr_left
  intro _
  constructor
  · intro h u hu hlt
    exact (pileWords_count cuts p v u hu).symm.trans (h u hlt)
  · intro h u hlt
    by_cases hu : u.get 0 = p
    · rw [pileWords_count cuts p v u hu]
      exact h u hu hlt
    · rw [pileWords_count_zero cuts p v u hu]
      symm
      apply Nat.eq_zero_of_le_zero
      calc
        observedCount (backwardWords cuts p ω) (j.val+1) u ≤ tupleCount (backwardWords cuts p ω) u := by
          apply Finset.card_le_card
          intro r hr
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.2⟩
        _ = 0 := (backwardWords_count cuts p ω u).trans (pileWords_count_zero cuts p ω u hu)

end RiffleUpperV2.Reservoir
