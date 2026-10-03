import RiffleUpperV2.Reservoir.SortedHistory

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile

local instance (priority := 2000) wordDecEq {k L : ℕ} : DecidableEq (Word k L) :=
  RiffleShuffle.wordLinearOrder.toDecidableEq

def pileWords {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) : Fin (pileSize cuts p) → Word k (L+1) :=
  fun r => sortedWord ω (pilePosition cuts p .forward r)

theorem pileWords_monotone {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) : Monotone (pileWords cuts p ω) := by
  intro r s hrs
  apply Tuple.monotone_sort (rowWord ω)
  change pileOffset cuts p + r.val ≤ pileOffset cuts p + s.val
  exact Nat.add_le_add_left hrs _

theorem pileWords_first {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (r : Fin (pileSize cuts p)) : (pileWords cuts p ω r).get 0 = p :=
  pilePosition_firstDigit cuts p .forward r ω

private theorem first_eq_iff_take_one {k L : ℕ} (w : Word k (L+1)) (p : Fin k) :
    w.get 0 = p ↔ w.toList.take 1 = [p] := by
  rcases w with ⟨l, hl⟩
  cases l with
  | nil => simp at hl
  | cons a l => simp [List.Vector.get]

theorem pilePosition_surjective_on_digit {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω : Sample cuts) (q : Fin n)
    (hq : (sortedWord ω q).get 0 = p) :
    ∃ r : Fin (pileSize cuts p), pilePosition cuts p .forward r = q := by
  have hp := (RiffleLowerV2.Model.prefixRanks cuts ω (pilePrefix (L := L) p)).1 q
  have hmem : (sortedWord ω q).toList.take 1 = [p] :=
    (first_eq_iff_take_one _ _).mp hq
  have hr := hp.mp hmem
  rw [pilePrefix_lowerRank, pilePrefix_upperRank] at hr
  refine ⟨⟨q.val-pileOffset cuts p, by omega⟩, ?_⟩
  apply Fin.ext
  change pileOffset cuts p + (q.val-pileOffset cuts p) = q.val
  omega

/-- Multiplicities in the named sorted pile are the actual labeled row counts.
This is where the first-digit constraint enters the sorted-history identity. -/
theorem pileWords_count {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (u : Word k (L+1)) (hu : u.get 0 = p) :
    tupleCount (pileWords cuts p ω) u =
      (Finset.univ.filter fun r : Fin n => rowWord ω r = u).card := by
  unfold tupleCount
  apply Finset.card_bij (fun r _ => RiffleLowerV2.stableSort ω (pilePosition cuts p .forward r))
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩
  · intro r _ s _ hrs
    have hh := (RiffleLowerV2.stableSort ω).injective hrs
    apply Fin.ext
    have hv := congrArg Fin.val hh
    change pileOffset cuts p + r.val = pileOffset cuts p + s.val at hv
    omega
  · intro r hr
    have hrow := (Finset.mem_filter.mp hr).2
    let q := (RiffleLowerV2.stableSort ω).symm r
    have hq : sortedWord ω q = u := by simpa [q, RiffleLowerV2.sortedWord] using hrow
    obtain ⟨s, hs⟩ := pilePosition_surjective_on_digit cuts p ω q (by rw [hq]; exact hu)
    refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change sortedWord ω (pilePosition cuts p .forward s) = u
      rwa [hs]
    · rw [hs]
      exact (RiffleLowerV2.stableSort ω).apply_symm_apply r

theorem pileWords_count_zero {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (u : Word k (L+1)) (hu : u.get 0 ≠ p) :
    tupleCount (pileWords cuts p ω) u = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro r _ hr
  exact hu (hr ▸ pileWords_first cuts p ω r)

def wordCount {k n L : ℕ} {cuts : Cuts k n L} (ω : Sample cuts) (u : Word k L) : ℕ :=
  (Finset.univ.filter fun r : Fin n => rowWord ω r = u).card

/-- Source eq:ub-exact-history-constraint for the actual frozen natural history.
The terminal word and its observed multiplicity are read from the representative
history. The last index j means that precisely j+1 words have been revealed. -/
theorem historyAtom {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω v : Sample cuts) (j : Fin (pileSize cuts p)) :
    historyFiber cuts p .forward (j.val+1) ω v ↔
      (∀ u : Word k (L+1), u.get 0 = p → u < pileWords cuts p ω j →
        wordCount v u = observedCount (pileWords cuts p ω) (j.val+1) u) ∧
      observedCount (pileWords cuts p ω) (j.val+1) (pileWords cuts p ω j) ≤
        wordCount v (pileWords cuts p ω j) := by
  have hh : historyFiber cuts p .forward (j.val+1) ω v ↔
      ∀ r : Fin (pileSize cuts p), r.val < j.val+1 →
        pileWords cuts p v r = pileWords cuts p ω r := by
    constructor
    · intro h r hr
      exact revealed_word_eq cuts p .forward (j.val+1) h r hr
    · intro h
      funext r
      by_cases hr : r.val < j.val+1
      · simp only [naturalHistory, hr, if_true]
        exact congrArg some (h r hr)
      · simp [naturalHistory, hr]
  rw [hh, sorted_history_iff _ _ (pileWords_monotone cuts p ω) (pileWords_monotone cuts p v)]
  rw [pileWords_count cuts p v _ (pileWords_first cuts p ω j)]
  change ((∀ u < pileWords cuts p ω j, tupleCount (pileWords cuts p v) u =
    observedCount (pileWords cuts p ω) (j.val+1) u) ∧ _) ↔ _
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
        observedCount (pileWords cuts p ω) (j.val+1) u ≤ tupleCount (pileWords cuts p ω) u :=
          by
            apply Finset.card_le_card
            intro r hr
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.2⟩
        _ = 0 := pileWords_count_zero cuts p ω u hu

end RiffleUpperV2.Reservoir
