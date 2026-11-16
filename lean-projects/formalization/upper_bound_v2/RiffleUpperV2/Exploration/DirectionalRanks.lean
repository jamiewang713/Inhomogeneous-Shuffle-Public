import RiffleUpperV2.Exploration.GuardConcentration
import RiffleUpperV2.Exploration.ReserveExistence

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open TimeProfile RiffleLowerV2.Model

/-- Taking a tail prefix preserves lexical order within a first-column pile. -/
theorem tailPrefix_mono_same_head {k L : ℕ} (D : ℕ) {s w : Word k (L+1)}
    (hhead : s.get 0 = w.get 0) (h : s ≤ w) : tailPrefix D s ≤ tailPrefix D w := by
  have ht := RiffleShuffle.take_lex_monotone (min D L+1) h
  change s.toList.take (min D L+1) ≤ w.toList.take (min D L+1) at ht
  rw [(tailBinPrefix_word D (s.get 0) (tailPrefix D s) s).mpr ⟨rfl,rfl⟩,
    (tailBinPrefix_word D (w.get 0) (tailPrefix D w) w).mpr ⟨rfl,rfl⟩] at ht
  change s.get 0 :: (tailPrefix D s).toList ≤ w.get 0 :: (tailPrefix D w).toList at ht
  rw [hhead] at ht
  rcases le_iff_eq_or_lt.mp ht with he | hl
  · exact (List.cons.inj he).2.le
  · exact le_of_lt (show tailPrefix D s < tailPrefix D w from List.lex_cons_iff.mp hl)

/-- Strict comparison of tail prefixes gives strict comparison of the full words. -/
theorem fullWord_lt_of_tailPrefix_lt {k L : ℕ} (D : ℕ) {s w : Word k (L+1)}
    (hhead : s.get 0 = w.get 0) (h : tailPrefix D s < tailPrefix D w) : s < w := by
  by_contra hh
  have hm := tailPrefix_mono_same_head D hhead.symm (le_of_not_gt hh)
  exact (not_lt_of_ge hm) h

/-- The spatially ordered tail-prefix tuple of an actual pile is monotone. -/
theorem pileTailPrefix_monotone {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ)
    (p : Fin k) (ω : Sample cuts) :
    Monotone (fun r : Fin (pileSize cuts p) => tailPrefix D (sortedWord ω (pilePosition cuts p .forward r))) := by
  intro r s hrs
  apply tailPrefix_mono_same_head D
  · rw [pilePosition_firstDigit, pilePosition_firstDigit]
  · apply Tuple.monotone_sort (rowWord ω)
    change pileOffset cuts p+r.val ≤ pileOffset cuts p+s.val
    exact Nat.add_le_add_left hrs _

/-- Reindex an arbitrary predicate on pile words by the actual spatial positions. -/
theorem pile_filter_card {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (Q : Word k (L+1) → Prop) :
    (Finset.univ.filter fun r : Fin (pileSize cuts p) => Q (sortedWord ω (pilePosition cuts p .forward r))).card =
      (Finset.univ.filter fun r : Fin n => (rowWord ω r).get 0 = p ∧ Q (rowWord ω r)).card := by
  apply Finset.card_bij (fun r _ => RiffleLowerV2.stableSort ω (pilePosition cuts p .forward r))
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, pilePosition_firstDigit cuts p .forward r ω,
      (Finset.mem_filter.mp hr).2⟩
  · intro r _ s _ hrs
    have hh := congrArg Fin.val ((RiffleLowerV2.stableSort ω).injective hrs)
    apply Fin.ext
    change pileOffset cuts p + r.val = pileOffset cuts p + s.val at hh
    omega
  · intro r hr
    obtain ⟨_, hp, hQ⟩ := Finset.mem_filter.mp hr
    let j := (RiffleLowerV2.stableSort ω).symm r
    have hjp : (sortedWord ω j).toList.take 1 = [p] := by
      change (rowWord ω (RiffleLowerV2.stableSort ω j)).toList.take 1 = [p]
      simp only [j, Equiv.apply_symm_apply]
      rw [row_take_one]
      simpa only [RiffleLowerV2.rowWord_get, sampleEntry, List.singleton_inj] using hp
    have hj := (RiffleLowerV2.Model.prefixRanks cuts ω (pilePrefix (L := L) p)).1 j |>.mp hjp
    rw [pilePrefix_lowerRank, pilePrefix_upperRank] at hj
    let t : Fin (pileSize cuts p) := ⟨j.val-pileOffset cuts p, by omega⟩
    have hpos : pilePosition cuts p .forward t = j := by
      apply Fin.ext
      change pileOffset cuts p + (j.val-pileOffset cuts p) = j.val
      omega
    refine ⟨t, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [hpos, RiffleLowerV2.sortedWord, j, Equiv.apply_symm_apply] using hQ
    · rw [hpos]
      exact Equiv.apply_symm_apply _ r

theorem guardCount_positions {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (p : Fin k) (ω : Sample cuts)
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (hv : chosenReserves cuts D g = some v) (through : Bool) :
    guardCount cuts D g p through ω =
      (Finset.univ.filter fun r : Fin (pileSize cuts p) =>
        if through then tailPrefix D (sortedWord ω (pilePosition cuts p .forward r)) ≤ v.2.1
        else tailPrefix D (sortedWord ω (pilePosition cuts p .forward r)) < v.2.1).card := by
  have hh := pile_filter_card cuts p ω (fun w => if through then tailPrefix D w ≤ v.2.1 else tailPrefix D w < v.2.1)
  cases through <;> simpa [guardCount, beforeMiddle, throughMiddle, hv] using hh.symm

theorem guard_before_rank {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (p : Fin k) (ω : Sample cuts)
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (hv : chosenReserves cuts D g = some v) (r : Fin (pileSize cuts p)) :
    r.val < guardCount cuts D g p false ω ↔
      tailPrefix D (sortedWord ω (pilePosition cuts p .forward r)) < v.2.1 := by
  rw [guardCount_positions cuts D g p ω v hv]
  simpa only [Bool.false_eq_true, if_false] using
    Tuple.lt_card_lt_iff_apply_lt_of_monotone (a := v.2.1) (j := r) (pileTailPrefix_monotone cuts D p ω)

theorem guard_through_rank {k n L : ℕ} (cuts : Cuts k n (L+1)) (D : ℕ) (g : ℝ)
    (p : Fin k) (ω : Sample cuts)
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (hv : chosenReserves cuts D g = some v) (r : Fin (pileSize cuts p)) :
    r.val < guardCount cuts D g p true ω ↔
      tailPrefix D (sortedWord ω (pilePosition cuts p .forward r)) ≤ v.2.1 := by
  rw [guardCount_positions cuts D g p ω v hv]
  simpa only [if_true] using
    Tuple.lt_card_le_iff_apply_le_of_monotone (a := v.2.1) (j := r) (pileTailPrefix_monotone cuts D p ω)

end RiffleUpperV2.Exploration
