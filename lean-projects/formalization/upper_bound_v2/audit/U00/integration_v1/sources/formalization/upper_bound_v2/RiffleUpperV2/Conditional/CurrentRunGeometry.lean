import RiffleUpperV2.Conditional.DirectionalGeometry
import RiffleUpperV2.Reservoir.BackwardHistory

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir
attribute [local instance 2000] Reservoir.wordDecEq

/-- The word tuple in the actual direction of revelation. -/
def revealWords {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (ω : Sample cuts) : Fin (pileSize cuts p) → Word k (L+1) :=
  fun r => sortedWord ω (pilePosition cuts p d r)

theorem revealWords_first {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (ω : Sample cuts) (r : Fin (pileSize cuts p)) :
    (revealWords cuts p d ω r).get 0=p := pilePosition_firstDigit cuts p d r ω

theorem revealWords_count {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (ω : Sample cuts) (s : Word k (L+1)) (hs : s.get 0=p) :
    tupleCount (revealWords cuts p d ω) s = wordCount ω s := by
  cases d
  · exact pileWords_count cuts p ω s hs
  · exact (backwardWords_count cuts p ω s).trans (pileWords_count cuts p ω s hs)

theorem observedCount_history {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (i : ℕ) (ω v : Sample cuts)
    (hv : historyFiber cuts p d i ω v) (s : Word k (L+1)) :
    observedCount (revealWords cuts p d v) i s=observedCount (revealWords cuts p d ω) i s := by
  apply congrArg Finset.card
  ext r
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hr : r.val < i
  · rw [show revealWords cuts p d v r=revealWords cuts p d ω r from
      revealed_word_eq cuts p d i hv r hr]
  · simp [hr]

/-- Each remaining edge in the currently exposed run consumes a distinct
unrevealed copy, including the crossing edge at time i. -/
theorem currentRun_count_le_excess {α : Type*} [DecidableEq α] {m : ℕ}
    (f : Fin m → α) (s : α) (i : ℕ) :
    (Finset.univ.filter fun e : Fin (m-1) => i≤e.val+1 ∧
      f ⟨e.val,by omega⟩=f ⟨e.val+1,by omega⟩ ∧ f ⟨e.val,by omega⟩=s).card ≤
      tupleCount f s-observedCount f i s := by
  have hsplit : (Finset.univ.filter fun r : Fin m => i≤r.val ∧ f r=s).card +
      observedCount f i s=tupleCount f s := by
    have hh := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun r : Fin m => f r=s) (p := fun r => i≤r.val)
    have h₁ : (Finset.univ.filter fun r : Fin m => f r=s).filter (fun r => i≤r.val) =
        Finset.univ.filter (fun r => i≤r.val ∧ f r=s) := by
      ext r
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact and_comm
    have h₂ : (Finset.univ.filter fun r : Fin m => f r=s).filter (fun r => ¬i≤r.val) =
        Finset.univ.filter (fun r => r.val < i ∧ f r=s) := by
      ext r
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,not_le]
      exact and_comm
    rw [h₁,h₂] at hh
    exact hh
  have hi : (Finset.univ.filter fun e : Fin (m-1) => i≤e.val+1 ∧
      f ⟨e.val,by omega⟩=f ⟨e.val+1,by omega⟩ ∧ f ⟨e.val,by omega⟩=s).card ≤
      (Finset.univ.filter fun r : Fin m => i≤r.val ∧ f r=s).card := by
    apply Finset.card_le_card_of_injOn (f := fun e : Fin (m-1) => (⟨e.val+1,by omega⟩ : Fin m))
    · intro e he
      obtain ⟨he,heq,hs⟩ := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,heq.symm.trans hs⟩
    · intro e _ e' _ hh
      apply Fin.ext
      have := congrArg Fin.val hh
      dsimp at this
      omega
  omega

def currentRunEdges {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (d : Direction) (i : ℕ) (s : Word k (L+1)) (ω : Sample cuts) :
    Finset (Fin (pileSize cuts p-1)) :=
  Finset.univ.filter fun e => i≤e.val+1 ∧
    revealWords cuts p d ω ⟨e.val,by omega⟩=revealWords cuts p d ω ⟨e.val+1,by omega⟩ ∧
    revealWords cuts p d ω ⟨e.val,by omega⟩=s

theorem currentRunEdges_card_le {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (i : ℕ) (ω v : Sample cuts)
    (hv : historyFiber cuts p d i ω v) (s : Word k (L+1)) (hs : s.get 0=p) :
    (currentRunEdges cuts p d i s v).card ≤
      wordCount v s-observedCount (revealWords cuts p d ω) i s := by
  have h := currentRun_count_le_excess (revealWords cuts p d v) s i
  rw [revealWords_count cuts p d v s hs,observedCount_history cuts p d i ω v hv s] at h
  exact h

end RiffleUpperV2.Conditional
