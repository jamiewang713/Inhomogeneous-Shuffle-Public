import RiffleUpperV2.GraphOverlap.RunProduct
import RiffleUpperV2.GraphOverlap.FactorialTail

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.GraphOverlap
open RiffleLowerV2 RiffleLowerV2.Model RiffleLowerV2.Factorial

theorem shuffle_componentSize {k N K : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) (i : Fin N) :
    (Finset.univ.filter fun j => componentKey (shuffleEdges ω) j =
      componentKey (shuffleEdges ω) i).card = wordCount (sortedWord ω i) ω := by
  rw [wordCount_eq_card, Fintype.card_subtype]
  apply Finset.card_bij (fun j _ => stableSort ω j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, componentKey_eq_iff,
      shuffle_componentIndex_eq_iff] at hj ⊢
    exact hj
  · intro j _ j' _ hj
    exact (stableSort ω).injective hj
  · intro j hj
    refine ⟨(stableSort ω).symm j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, componentKey_eq_iff,
      shuffle_componentIndex_eq_iff]
    simpa only [RiffleLowerV2.sortedWord, Equiv.apply_symm_apply] using
      (Finset.mem_filter.mp hj).2

theorem boundedComponents_shuffle_iff {k N K B : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) : BoundedComponents (shuffleEdges ω) B ↔
      ∀ w : Word k K, wordCount w ω ≤ B := by
  constructor
  · intro h w
    by_cases hw : wordCount w ω = 0
    · simp [hw]
    · have hpos : 0 < wordCount w ω := Nat.pos_of_ne_zero hw
      rw [wordCount_eq_card, Fintype.card_subtype] at hpos
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
      let i := (stableSort ω).symm j
      have hi : sortedWord ω i = w := by
        simpa [RiffleLowerV2.sortedWord, i] using (Finset.mem_filter.mp hj).2
      rw [← hi, ← shuffle_componentSize ω i]
      exact h _
  · intro h c
    by_cases he : (Finset.univ.filter fun i => componentKey (shuffleEdges ω) i = c).Nonempty
    · obtain ⟨i, hi⟩ := he
      have hc := (Finset.mem_filter.mp hi).2
      rw [← hc, shuffle_componentSize]
      exact h _
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp

theorem not_boundedComponents_shuffle {k N K B : ℕ} {cuts : Cuts k N K}
    (ω : Sample cuts) : ¬ BoundedComponents (shuffleEdges ω) B ↔
      ∃ w : Word k K, B+1 ≤ wordCount w ω := by
  rw [boundedComponents_shuffle_iff]
  push Not
  simp only [Nat.succ_le_iff]

theorem centralBinomial_one_le (B : ℕ) : (1 : ℝ) ≤ (B.choose (B/2) : ℝ) := by
  exact_mod_cast Nat.choose_pos (Nat.div_le_self B 2)

end RiffleUpperV2.GraphOverlap
