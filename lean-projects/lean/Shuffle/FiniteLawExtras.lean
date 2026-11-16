import Shuffle.FiniteLaw

noncomputable section
open scoped BigOperators

namespace Shuffle.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (p : FiniteLaw Ω)

/-- F1 for arbitrary finite families, including the empty family. -/
theorem prob_exists_le_sum {ι : Type*} [Fintype ι] (E : ι → Ω → Prop) :
    p.prob (fun ω => ∃ i, E i ω) ≤ ∑ i, p.prob (E i) := by
  classical
  unfold prob
  calc
    _ ≤ ∑ ω, ∑ i, if E i ω then p.mass ω else 0 := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases h : ∃ i, E i ω
      · simp only [h, ↓reduceIte]
        obtain ⟨i, hi⟩ := h
        have hs := Finset.single_le_sum
          (f := fun j => if E j ω then p.mass ω else 0)
          (fun j (_ : j ∈ (Finset.univ : Finset ι)) => by
            dsimp only
            split_ifs <;> simp [p.mass_nonneg ω]) (Finset.mem_univ i)
        simpa only [if_pos hi] using hs
      · simp only [h, ↓reduceIte]
        apply Finset.sum_nonneg
        intro i _
        split_ifs <;> simp [p.mass_nonneg ω]
    _ = _ := Finset.sum_comm

/-- H0: the finite event probability agrees with the mathlib measure. -/
theorem measure_toPMF [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (E : Ω → Prop) :
    p.toPMF.toMeasure {ω | E ω} = ENNReal.ofReal (p.prob E) := by
  classical
  rw [p.toPMF.toMeasure_apply_of_finite {ω | E ω} (Set.toFinite _), tsum_fintype]
  unfold prob
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro ω _
    by_cases h : E ω <;> simp [Set.indicator, h]
  · intro ω _
    split_ifs
    · exact p.mass_nonneg ω
    · exact le_rfl

end Shuffle.FiniteLaw
