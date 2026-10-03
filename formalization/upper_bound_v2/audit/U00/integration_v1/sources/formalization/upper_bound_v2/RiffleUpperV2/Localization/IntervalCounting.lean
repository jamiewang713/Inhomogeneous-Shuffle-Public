import RiffleUpperV2.Localization.Scalars

noncomputable section
namespace RiffleUpperV2.Localization

/-- Two outer enlarged intervals cannot surround a third interval longer than 2w. -/
theorem no_three_enlarged_intervals {l₁ r₁ l₂ r₂ l₃ r₃ m w : ℝ}
    (h₁₂ : r₁ ≤ l₂) (h₂₃ : r₂ ≤ l₃) (hlen : 2*w < r₂-l₂)
    (hfirst : m ≤ r₁+w) (hlast : l₃-w ≤ m) : False := by
  linarith

/-- At a fixed depth, ordered disjoint parent mean intervals have multiplicity two. -/
theorem enlargedIntervalMultiplicity {α : Type*} [LinearOrder α]
    (s : Finset α) (left right : α → ℝ) (m w : ℝ)
    (hordered : ∀ i ∈ s, ∀ j ∈ s, i < j → right i ≤ left j)
    (hlength : ∀ i ∈ s, 2*w < right i-left i)
    (hmember : ∀ i ∈ s, left i-w ≤ m ∧ m ≤ right i+w) : s.card ≤ 2 := by
  classical
  let f : α → Bool := fun i => decide (left i + right i ≤ 2*m)
  have hinj : (s : Set α).InjOn f := by
    intro i hi j hj heq
    by_contra hne
    have ordered_contra {i j : α} (hi : i ∈ s) (hj : j ∈ s)
        (hij : i < j) (heq : f i = f j) : False := by
      have hord := hordered i hi j hj hij
      have hli := hlength i hi
      have hlj := hlength j hj
      have hmi := hmember i hi
      have hmj := hmember j hj
      by_cases hmid : left i + right i ≤ 2*m
      · have hmidj : left j + right j ≤ 2*m := by
          simpa [f,hmid] using heq.symm
        linarith
      · have hmidj : ¬ left j + right j ≤ 2*m := by
          simpa [f,hmid] using heq.symm
        linarith
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ordered_contra hi hj hij heq
    · exact ordered_contra hj hi hji heq.symm
  have hc := Finset.card_le_card_of_injOn f
    (show Set.MapsTo f s (Finset.univ : Finset Bool) from fun _ _ => Finset.mem_univ _) hinj
  simpa using hc

/-- Finite class summation retains the number of discarded blocks explicitly. -/
theorem discarded_sum_le_card_mul {α : Type*} (s : Finset α) (p : α → ℝ) (ε : ℝ)
    (hp : ∀ i ∈ s, p i ≤ ε) : ∑ i ∈ s, p i ≤ (s.card : ℝ) * ε := by
  calc
    _ ≤ ∑ _i ∈ s, ε := Finset.sum_le_sum hp
    _ = _ := by simp

end RiffleUpperV2.Localization
