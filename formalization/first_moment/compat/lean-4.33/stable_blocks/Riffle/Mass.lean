import Riffle.Model
import Riffle.Words

namespace Riffle

/-- F01: each legal full word has positive marginal mass. -/
theorem weight_pos {D : Model} (ω : FullIndex D) (h : Legal D (fullList ω)) :
    0 < weight D ω := by
  unfold weight
  apply Finset.prod_pos
  intro i _
  apply (prob_pos_iff D i (ω i)).mpr
  have hh := (h.2 i (by simpa [fullList_length] using i.isLt)).2
  simpa only [fullList_digit ω i.isLt] using hh

/-- F01: an illegal alphabet-bounded full word has zero marginal mass. -/
theorem weight_eq_zero_of_not_legal {D : Model} (ω : FullIndex D)
    (h : ¬ Legal D (fullList ω)) : weight D ω = 0 := by
  classical
  have hn : ∃ i : Fin D.K, D.n i (ω i) = 0 := by
    by_contra he
    apply h
    refine ⟨by simp [fullList_length], ?_⟩
    intro i hi
    have hiK : i < D.K := by simpa [fullList_length] using hi
    rw [fullList_digit ω hiK]
    refine ⟨(ω ⟨i, hiK⟩).isLt, ?_⟩
    have hne : D.n i (ω ⟨i, hiK⟩) ≠ 0 := fun hz => he ⟨⟨i, hiK⟩, hz⟩
    exact Nat.pos_of_ne_zero hne
  obtain ⟨i, hi⟩ := hn
  unfold weight
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [prob, hi]

theorem expectedCount_pos {D : Model} {E : Set Word} {x : Word}
    (hx : Full D x) (hE : x ∈ E) : 0 < expectedCount D E := by
  classical
  obtain ⟨ω, hω⟩ := fullList_of_full hx
  have hp : 0 < weight D ω := weight_pos ω (hω.symm ▸ hx.1)
  unfold expectedCount
  apply mul_pos
  · exact_mod_cast (lt_trans Nat.zero_lt_one D.one_lt_N)
  · apply lt_of_lt_of_le (b := (if fullList ω ∈ E then weight D ω else 0))
    · simpa only [hω, if_pos hE] using hp
    · exact Finset.single_le_sum (f := fun θ : FullIndex D =>
        if fullList θ ∈ E then weight D θ else 0) (fun _ _ => zero_le) (Finset.mem_univ ω)

theorem sum_weight (D : Model) : ∑ ω : FullIndex D, weight D ω = 1 := by
  classical
  unfold weight FullIndex
  rw [← Fintype.prod_sum (fun (i : Fin D.K) (a : Fin D.k) => prob D i a)]
  have hs : ∀ i : Fin D.K, ∑ a : Fin D.k, prob D i a = 1 := by
    intro i
    simpa only [Fin.sum_univ_eq_sum_range] using sum_prob D i i.isLt
  simp only [hs, Finset.prod_const_one]

theorem expectedCount_full (D : Model) : expectedCount D {x | Full D x} = D.N := by
  classical
  have hs : (∑ ω : FullIndex D, if fullList ω ∈ {x | Full D x} then weight D ω else 0) =
      ∑ ω : FullIndex D, weight D ω := by
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : Legal D (fullList ω)
    · simp only [Set.mem_setOf_eq, Full, h, fullList_length, and_self, if_true]
    · simp only [Set.mem_setOf_eq, Full, h, false_and, if_false,
        weight_eq_zero_of_not_legal ω h]
  rw [expectedCount, hs, sum_weight, mul_one]

end Riffle
