import RiffleUpperV2.Localization.RelevantParents

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization

/-- Probability loss from all nonrelevant proper leaves, retaining the full word count. -/
theorem irrelevantLoss_finite {k n d : ℕ} (N : ℕ) (hk : 0 < k) (cuts : Cuts k n d)
    (c₀ : ℤ) (R : Finset (Fin n)) (v : Prefix k d) (δ ε : ℝ) (hε : 0 ≤ ε) (m : ℤ) :
    probability (fixedCountPMF cuts) (fun ω => ∃ x : Prefix k d,
      ProperStable N cuts R v δ x ∧ ¬Relevant cuts c₀ R m ε x ∧ m ∈ anchoredInterval c₀ R x ω) ≤
      ((d+1)*k^d : ℕ)*ε := by
  calc
    _ ≤ ∑ x : Prefix k d, probability (fixedCountPMF cuts) (fun ω =>
        ProperStable N cuts R v δ x ∧ ¬Relevant cuts c₀ R m ε x ∧ m ∈ anchoredInterval c₀ R x ω) :=
      RiffleLowerV2.Thinning.probability_iUnion_le _ _
    _ ≤ ∑ _x : Prefix k d, ε := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hrel : Relevant cuts c₀ R m ε x
      · simp only [hrel,not_true_eq_false,false_and,and_false]
        simpa [RiffleUpperV2.probability,RiffleLowerV2.probability,RiffleLowerV2.expect] using hε
      · exact (RiffleLowerV2.Thinning.probability_mono _ (fun _ h => h.2.2)).trans
          (le_of_lt (lt_of_not_ge hrel))
    _ = (Fintype.card (Prefix k d) : ℝ)*ε := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast prefix_card_bound k d hk) hε

/-- The source omitted-cover event is contained in the same finite union. -/
theorem irrelevantLoss {k n d : ℕ} (N : ℕ) (hk : 0 < k) (cuts : Cuts k n d)
    (c₀ : ℤ) (R : Finset (Fin n)) (v : Prefix k d) (δ ε : ℝ) (hε : 0 ≤ ε) (m : ℤ) :
    probability (fixedCountPMF cuts) (fun ω =>
      (∃ x, ProperStable N cuts R v δ x ∧ m ∈ anchoredInterval c₀ R x ω) ∧
      ¬∃ x, ProperStable N cuts R v δ x ∧ Relevant cuts c₀ R m ε x ∧ m ∈ anchoredInterval c₀ R x ω) ≤
      ((d+1)*k^d : ℕ)*ε := by
  apply (RiffleLowerV2.Thinning.probability_mono _ ?_).trans
    (irrelevantLoss_finite N hk cuts c₀ R v δ ε hε m)
  rintro ω ⟨⟨x,hx,hm⟩,hno⟩
  exact ⟨x,hx,fun hr => hno ⟨x,hx,hr,hm⟩,hm⟩

end RiffleUpperV2.Localization
