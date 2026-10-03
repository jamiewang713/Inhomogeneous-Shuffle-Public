import RiffleUpperV2.Anchor.EqualMeasurability

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Anchor
open TimeProfile

def equalSampleRows {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) : Finset (Fin n) :=
  matchingBeforeRows R x j ω \ equalityRows (x.2.get j) (ω (prefixColumn x j))

theorem equalSampleRows_subset {k n d : ℕ} {cuts : Cuts k n d} (R : Finset (Fin n))
    (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    equalSampleRows R x j ω ⊆ Finset.univ \ equalityRows (x.2.get j) (ω (prefixColumn x j)) := by
  exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)

theorem equalSampleRows_eq_of_equalReveal {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) :
    equalSampleRows R x j ω = equalSampleRows R x j ω₀ := by
  unfold equalSampleRows
  rw [matchingBeforeRows_eq_of_equalReveal R x j hf, hf.2]

theorem equalRandomRows_eq {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    equalRandomRows R x j ω = equalSampleRows R x j ω ∩
      residualAllowed (equalityRows (x.2.get j) (ω (prefixColumn x j)))
        (Finset.univ.filter (· < x.2.get j)) (ω (prefixColumn x j)) := by
  apply Finset.ext
  intro r
  unfold equalRandomRows equalSampleRows matchingBeforeRows residualAllowed equalityRows
  change (r ∈ R.filter (fun t => rowSlice ω t 0 j.val = x.2.toList.take j.val ∧
    (ω (prefixColumn x j)).val t < x.2.get j)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hr,ht,hd⟩
    exact ⟨⟨⟨hr,ht⟩, ne_of_lt hd⟩, hd, ne_of_lt hd⟩
  · rintro ⟨⟨⟨hr,ht⟩,_⟩,hd,_⟩
    exact ⟨hr,ht,hd⟩

/-- Conditional expectations only use values on the conditioning fiber. -/
theorem conditionalExpect_congr_on {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (E : Ω → Prop) {f g : Ω → ℝ} (h : ∀ ω, E ω → f ω = g ω) :
    RiffleLowerV2.conditionalExpect P f E = RiffleLowerV2.conditionalExpect P g E := by
  unfold RiffleLowerV2.conditionalExpect RiffleLowerV2.expect
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : E ω
  · simp only [he, if_true, h ω he]
  · simp only [he, if_false]

/-- The actual source parameters for the coincident-side case. -/
def equalEndpointParams {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω₀ : Sample cuts) :=
  sourceSamplingParams (equalityRows (x.2.get j) (ω₀ (prefixColumn x j)))
    (equalSampleRows R x j ω₀) (Finset.univ.filter (· < x.2.get j))
    (ω₀ (prefixColumn x j)) (equalSampleRows_subset R x j ω₀)

/-- Exact endpoint law in the equal-maximizer reveal, for every legal or
nonlegal continuation containing j. The two endpoints have the same random
hypergeometric displacement and revealed shifts, including when x is the join. -/
theorem endpointShiftHypergeometric_equal {k n d : ℕ} (cuts : Cuts k n d)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val)
    (ω₀ : Sample cuts) (f : ℤ → ℝ) :
    RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (lowerEndpoint c₀ R x ω))
      (equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀) =
      expect (equalEndpointParams R x j ω₀).law.toPMF
        (fun q => f (equalShift c₀ R x j ω₀ + q.val)) ∧
    RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (upperEndpoint c₀ R x ω))
      (equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀) =
      expect (equalEndpointParams R x j ω₀).law.toPMF
        (fun q => f (equalShift c₀ R x j ω₀ + q.val + (prefixRows R x ω₀).card)) := by
  have hy (ω : Sample cuts)
      (hf : equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀ ω) :
      equalRandomRows R x j ω = equalSampleRows R x j ω₀ ∩
        residualAllowed (equalityRows (x.2.get j) (ω₀ (prefixColumn x j)))
          (Finset.univ.filter (· < x.2.get j)) (ω (prefixColumn x j)) := by
    rw [equalRandomRows_eq, equalSampleRows_eq_of_equalReveal R x j hf, hf.2]
  constructor
  · trans RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (equalShift c₀ R x j ω₀ +
        ((equalSampleRows R x j ω₀ ∩ residualAllowed
          (equalityRows (x.2.get j) (ω₀ (prefixColumn x j)))
          (Finset.univ.filter (· < x.2.get j)) (ω (prefixColumn x j))).card : ℤ)))
      (equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀)
    · apply conditionalExpect_congr_on
      intro ω hf
      rw [(equal_endpoint_shift c₀ R x j ω).1,
        (equalShift_eq_of_equalReveal c₀ R x j hf).1, hy ω hf]
    · exact equalRevealConditionalExpect cuts (prefixColumn x j) (x.2.get j)
        (equalSampleRows R x j ω₀) ω₀ (equalSampleRows_subset R x j ω₀)
        (fun q => f (equalShift c₀ R x j ω₀ + q))
  · trans RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (equalShift c₀ R x j ω₀ +
        ((equalSampleRows R x j ω₀ ∩ residualAllowed
          (equalityRows (x.2.get j) (ω₀ (prefixColumn x j)))
          (Finset.univ.filter (· < x.2.get j)) (ω (prefixColumn x j))).card : ℤ) +
        (prefixRows R x ω₀).card))
      (equalRevealFiber (prefixColumn x j) (x.2.get j) ω₀)
    · apply conditionalExpect_congr_on
      intro ω hf
      rw [(equal_endpoint_shift c₀ R x j ω).2,
        (equalShift_eq_of_equalReveal c₀ R x j hf).1,
        (equalShift_eq_of_equalReveal c₀ R x j hf).2, hy ω hf]
    · exact equalRevealConditionalExpect cuts (prefixColumn x j) (x.2.get j)
        (equalSampleRows R x j ω₀) ω₀ (equalSampleRows_subset R x j ω₀)
        (fun q => f (equalShift c₀ R x j ω₀ + q + (prefixRows R x ω₀).card))

end RiffleUpperV2.Anchor
