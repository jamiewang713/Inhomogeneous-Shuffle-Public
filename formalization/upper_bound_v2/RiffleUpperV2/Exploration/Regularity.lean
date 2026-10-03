import RiffleUpperV2.Exploration.HistoryProbability

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open RiffleLowerV2.Thinning

@[simp] theorem direction_card : Fintype.card Direction = 2 := by
  rw [Fintype.card, show (Finset.univ : Finset Direction) = {.forward, .backward} from rfl]
  simp

def HistoryIndex {k n L : ℕ} (cuts : Cuts k n (L+1)) :=
  Σ p : Fin k, Direction × Fin (pileSize cuts p)

instance {k n L : ℕ} (cuts : Cuts k n (L+1)) : Fintype (HistoryIndex cuts) :=
  inferInstanceAs (Fintype (Σ p : Fin k, Direction × Fin (pileSize cuts p)))

theorem historyIndex_card {k n L : ℕ} (cuts : Cuts k n (L+1)) :
    Fintype.card (HistoryIndex cuts) = 2*n := by
  change Fintype.card (Σ p : Fin k, Direction × Fin (pileSize cuts p)) = _
  simp only [Fintype.card_sigma, Fintype.card_prod, direction_card, Fintype.card_fin]
  rw [← Finset.mul_sum]
  exact congrArg (2 * ·) (cuts.sum_count 0)

/-- Union over separate histories. The counting cost is 2N, even with empty piles. -/
theorem historyGood_unionBound {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ r : ℝ) (hr : 0 < r)
    (hH : probability (fixedCountPMF cuts) (fun ω => ¬ concentrationEvent cuts D g ξ ω) ≤ r) :
    probability (fixedCountPMF cuts) (fun ω => ∃ q : HistoryIndex cuts,
      ¬ historyGood cuts D g ξ (Real.sqrt r) q.1 q.2.1 q.2.2.val ω) ≤
        2*n * Real.sqrt r := by
  calc
    _ ≤ ∑ q : HistoryIndex cuts, probability (fixedCountPMF cuts)
        (fun ω => ¬ historyGood cuts D g ξ (Real.sqrt r) q.1 q.2.1 q.2.2.val ω) :=
      probability_iUnion_le _ _
    _ ≤ ∑ _ : HistoryIndex cuts, Real.sqrt r :=
      Finset.sum_le_sum (fun q _ => historyGoodProbability cuts D g ξ r hr hH q.1 q.2.1 q.2.2.val)
    _ = _ := by simp [historyIndex_card, Nat.cast_mul]

/-- Assembly only: concentration and small-pile failure still require their model proofs. -/
theorem regularityFailure_of_bounds {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ r s : ℝ) (hr : 0 < r)
    (hH : probability (fixedCountPMF cuts) (fun ω => ¬ concentrationEvent cuts D g ξ ω) ≤ r)
    (hsmall : probability (fixedCountPMF cuts) (fun ω =>
      ∃ p, (pileSize cuts p : ℝ) < (n : ℝ)^ξ ∧ ¬ pileEdgeFree cuts p ω) ≤ s) :
    probability (fixedCountPMF cuts) (fun ω => ¬ regularityEvent cuts D g ξ (Real.sqrt r) ω) ≤
      r + 2*n * Real.sqrt r + s := by
  let B : Sample cuts → Prop := fun ω => ∃ q : HistoryIndex cuts,
    ¬ historyGood cuts D g ξ (Real.sqrt r) q.1 q.2.1 q.2.2.val ω
  let S : Sample cuts → Prop := fun ω =>
    ∃ p, (pileSize cuts p : ℝ) < (n : ℝ)^ξ ∧ ¬ pileEdgeFree cuts p ω
  have hc : ∀ ω, ¬ regularityEvent cuts D g ξ (Real.sqrt r) ω →
      ¬ concentrationEvent cuts D g ξ ω ∨ B ω ∨ S ω := by
    intro ω h
    by_cases hHω : concentrationEvent cuts D g ξ ω
    · right
      by_cases hB : B ω
      · exact Or.inl hB
      · right
        by_contra hS
        apply h
        refine ⟨hHω, ?_, ?_⟩
        · intro p d i _ hi
          by_contra hbad
          exact hB ⟨⟨p, d, ⟨i, hi⟩⟩, hbad⟩
        · intro p hp
          by_contra hbad
          exact hS ⟨p, hp, hbad⟩
    · exact Or.inl hHω
  calc
    _ ≤ probability (fixedCountPMF cuts) (fun ω => ¬ concentrationEvent cuts D g ξ ω ∨ B ω ∨ S ω) :=
      probability_mono _ hc
    _ ≤ probability (fixedCountPMF cuts) (fun ω => ¬ concentrationEvent cuts D g ξ ω) +
        probability (fixedCountPMF cuts) (fun ω => B ω ∨ S ω) := probability_union_le _ _ _
    _ ≤ r + (probability (fixedCountPMF cuts) B + probability (fixedCountPMF cuts) S) :=
      add_le_add hH (probability_union_le _ _ _)
    _ ≤ r + (2*n * Real.sqrt r + s) :=
      add_le_add (le_refl r) (add_le_add (historyGood_unionBound cuts D g ξ r hr hH) hsmall)
    _ = _ := by ring

end RiffleUpperV2.Exploration
