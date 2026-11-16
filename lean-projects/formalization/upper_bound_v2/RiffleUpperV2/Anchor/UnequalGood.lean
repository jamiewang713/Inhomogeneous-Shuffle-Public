import RiffleUpperV2.Anchor.WitnessInclusion
import RiffleUpperV2.Anchor.ResidualOtherTail

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile Hypergeometric RiffleLowerV2.Thinning

theorem unequalExposed_otherDetermined {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) :
    OtherDetermined (prefixColumn x j) (unequalExposedRows (cuts := cuts) s R x j) :=
  fun _ _ h => (other_unequalRows s R x j h).2

theorem unequalExposed_subset {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    unequalExposedRows s R x j ω ⊆ R :=
  (Finset.sdiff_subset).trans (Finset.filter_subset _ _)

theorem unequalTotal_card_le {k n d : ℕ} {cuts : Cuts k n d}
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    (unequalExposedRows s R x j ω).card + (unequalSampleRows s R x j ω).card ≤ R.card := by
  have hB : unequalSampleRows s R x j ω ⊆ matchingBeforeRows R x j ω := Finset.filter_subset _ _
  have he : (unequalExposedRows s R x j ω).card =
      (matchingBeforeRows R x j ω).card - (unequalSampleRows s R x j ω).card :=
    Finset.card_sdiff_of_subset hB
  have ht : (matchingBeforeRows R x j ω).card ≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hb := Finset.card_le_card hB
  omega

/-- The three actual source lower-count conditions, with the source B0
witness and random residual marked and unmarked counts. -/
def unequalGood {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val) (ω : Sample cuts) : Prop :=
  witnessMean cuts s R x i j / 2 ≤ (witnessRows cuts s R x i j ω).card ∧
  residualMean cuts (prefixColumn x j) (unequalExposedRows s R x j ω) (s.allowed (x.2.get j))/2 ≤
    (residualAllowed (unequalExposedRows s R x j ω) (s.allowed (x.2.get j)) (ω (prefixColumn x j))).card ∧
  residualMean cuts (prefixColumn x j) (unequalExposedRows s R x j ω) (Finset.univ \ s.allowed (x.2.get j))/2 ≤
    (residualAllowed (unequalExposedRows s R x j ω) (Finset.univ \ s.allowed (x.2.get j))
      (ω (prefixColumn x j))).card

theorem unequalGood_measurable {k n d : ℕ} (cuts : Cuts k n d) (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : unequalRevealFiber s R x j ω₀ ω) :
    unequalGood cuts s R x i j ω ↔ unequalGood cuts s R x i j ω₀ := by
  have hr (D : Finset (Fin k)) :
      (residualAllowed (unequalExposedRows s R x j ω) D (ω (prefixColumn x j))).card =
      (residualAllowed (unequalExposedRows s R x j ω₀) D (ω₀ (prefixColumn x j))).card := by
    rw [(other_unequalRows s R x j hf.1).2]
    exact (residualAllowed_card _ D _ _ hf.2).trans
      (residualAllowed_card _ D _ _ (fun _ _ => rfl)).symm
  unfold unequalGood
  rw [witnessRows_other_invariant cuts s R x i j hf.1, hr, hr,
    (other_unequalRows s R x j hf.1).2]

/-- Actual failure probability before deterministic comparison of the means. -/
theorem unequalGood_failure_raw {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (s : SuffixSide) (R : Finset (Fin n)) (x : Prefix k d) (i j : Fin x.1.val)
    {g : ℝ} (hg : Reserve R g) :
    probability (fixedCountPMF cuts) (fun ω => ¬ unequalGood cuts s R x i j ω) ≤
      Real.exp (-RiffleLowerV2.chernoffConstant * witnessMean cuts s R x i j) +
      Real.exp (-RiffleLowerV2.chernoffConstant * g * allowedCount cuts (prefixColumn x j) (s.allowed (x.2.get j))) +
      Real.exp (-RiffleLowerV2.chernoffConstant * g * allowedCount cuts (prefixColumn x j)
        (Finset.univ \ s.allowed (x.2.get j))) := by
  let F₀ := fun ω => ((witnessRows cuts s R x i j ω).card : ℝ) ≤ witnessMean cuts s R x i j/2
  let F₁ := residualHalfFailure cuts (prefixColumn x j) (unequalExposedRows s R x j) (s.allowed (x.2.get j))
  let F₂ := residualHalfFailure cuts (prefixColumn x j) (unequalExposedRows s R x j) (Finset.univ \ s.allowed (x.2.get j))
  have hb : probability (fixedCountPMF cuts) F₀ ≤
      Real.exp (-RiffleLowerV2.chernoffConstant * witnessMean cuts s R x i j) := by
    exact (anchorCylinderTail cuts R (witnessDigits s x i j) (t := 1) (by norm_num)).2
  have h₁ := residualHalfFailure_bound cuts hn (prefixColumn x j) R
    (unequalExposedRows s R x j) (unequalExposed_otherDetermined s R x j)
    (unequalExposed_subset s R x j) (s.allowed (x.2.get j)) hg
  have h₂ := residualHalfFailure_bound cuts hn (prefixColumn x j) R
    (unequalExposedRows s R x j) (unequalExposed_otherDetermined s R x j)
    (unequalExposed_subset s R x j) (Finset.univ \ s.allowed (x.2.get j)) hg
  apply (probability_mono (fixedCountPMF cuts) (B := fun ω => (F₀ ω ∨ F₁ ω) ∨ F₂ ω) ?_).trans
  · apply (probability_union_le (fixedCountPMF cuts) _ _).trans
    exact add_le_add ((probability_union_le (fixedCountPMF cuts) _ _).trans (add_le_add hb h₁)) h₂
  · intro ω hh
    change ¬ (_ ∧ _ ∧ _) at hh
    rcases not_and_or.mp hh with h | h
    · exact Or.inl (Or.inl (not_le.mp h).le)
    · rcases not_and_or.mp h with h | h
      · exact Or.inl (Or.inr (not_le.mp h).le)
      · exact Or.inr (not_le.mp h).le

end RiffleUpperV2.Anchor
