import RiffleUpperV2.Exploration.Objects
import RiffleLowerV2.Model.Sorting

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open TimeProfile

private theorem singleton_lt_iff {k : ℕ} (a b : Fin k) : ([a] : List (Fin k)) < [b] ↔ a < b := by
  constructor
  · intro h
    cases h with
    | rel h => exact h
    | cons h => cases h
  · exact List.Lex.rel

def pilePrefix {k L : ℕ} (p : Fin k) : Prefix k (L+1) :=
  ⟨⟨1, by omega⟩, ⟨[p], rfl⟩⟩

theorem row_take_one {k n L : ℕ} {cuts : Cuts k n (L+1)} (ω : Sample cuts) (r : Fin n) :
    (rowWord ω r).toList.take 1 = [(ω 0).val r] := by
  simp [RiffleLowerV2.rowWord, List.ofFn_succ, sampleRow, sampleEntry]

theorem pilePrefix_count {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω : Sample cuts) : RiffleLowerV2.prefixCount (pilePrefix (L := L) p) ω = pileSize cuts p := by
  change (Finset.univ.filter fun r : Fin n =>
    (rowWord ω r).toList.take 1 = [p]).card = cuts.count 0 p
  simp_rw [row_take_one, List.singleton_inj]
  exact (ω 0).property p

theorem pilePrefix_lowerRank {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω : Sample cuts) : RiffleLowerV2.lowerRank (pilePrefix (L := L) p) ω = pileOffset cuts p := by
  change (Finset.univ.filter fun r : Fin n =>
    (rowWord ω r).toList.take 1 < [p]).card = _
  simp_rw [row_take_one, singleton_lt_iff]
  have hcard := Finset.sum_card_fiberwise_eq_card_filter
    (t := Finset.univ.filter (fun q : Fin k => q < p))
    (s := (Finset.univ : Finset (Fin n))) (g := fun r => (ω 0).val r)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcard
  rw [← hcard]
  unfold pileOffset
  exact Finset.sum_congr rfl (fun q _ => (ω 0).property q)

theorem pilePrefix_upperRank {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (ω : Sample cuts) :
    RiffleLowerV2.upperRank (pilePrefix (L := L) p) ω = pileOffset cuts p + pileSize cuts p := by
  have hr := (RiffleLowerV2.Model.prefixRanks cuts ω (pilePrefix (L := L) p)).2
  rw [pilePrefix_count cuts p ω, pilePrefix_lowerRank cuts p ω] at hr
  have hl : RiffleLowerV2.lowerRank (pilePrefix (L := L) p) ω ≤ RiffleLowerV2.upperRank (pilePrefix (L := L) p) ω := by
    apply Finset.card_le_card
    intro r hr
    simp only [RiffleLowerV2.lowerRank, RiffleLowerV2.upperRank, Finset.mem_filter,
      Finset.mem_univ, true_and] at hr ⊢
    exact hr.le
  rw [pilePrefix_lowerRank cuts p ω] at hl
  omega

/-- The absolute position convention really selects exactly the named first-column pile. -/
theorem pilePosition_firstDigit {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) (r : Fin (pileSize cuts p)) (ω : Sample cuts) :
    (sortedWord ω (pilePosition cuts p d r)).get 0 = p := by
  have hr := (RiffleLowerV2.Model.prefixRanks cuts ω (pilePrefix (L := L) p)).1
    (pilePosition cuts p d r)
  have hpos : RiffleLowerV2.lowerRank (pilePrefix (L := L) p) ω ≤ (pilePosition cuts p d r).val ∧
      (pilePosition cuts p d r).val < RiffleLowerV2.upperRank (pilePrefix (L := L) p) ω := by
    rw [pilePrefix_lowerRank, pilePrefix_upperRank]
    constructor
    · simp [pilePosition]
    · exact Nat.add_lt_add_left (spatialIndex d r).isLt _
  have hw := hr.mpr hpos
  change (rowWord ω (RiffleLowerV2.stableSort ω (pilePosition cuts p d r))).toList.take 1 = [p] at hw
  rw [row_take_one, List.singleton_inj] at hw
  simpa only [RiffleLowerV2.sortedWord, RiffleLowerV2.rowWord_get, sampleEntry] using hw

end RiffleUpperV2.Exploration
