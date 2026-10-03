import RiffleUpperV2.Anchor.UnequalMeasurability

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

def unequalEndpointParams {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω₀ : Sample cuts) :=
  sourceSamplingParams (unequalExposedRows s R x j ω₀) (unequalSampleRows s R x j ω₀)
    (s.allowed (x.2.get j)) (ω₀ (prefixColumn x j)) (unequalSampleRows_subset s R x j ω₀)

/-- Both unequal orientations on the actual matrix law. The random exposed
set is constant on each other-column atom, as proved in other_unequalRows. -/
theorem endpointShiftHypergeometric_unequal {k n d : ℕ} (cuts : Cuts k n d)
    (s : SuffixSide) (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val)
    (ω₀ : Sample cuts) (f : ℤ → ℝ) :
    RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (lowerEndpoint c₀ R x ω)) (unequalRevealFiber s R x j ω₀) =
      expect (unequalEndpointParams s R x j ω₀).law.toPMF
        (fun q => f (unequalShift s c₀ R x j ω₀ + q.val)) ∧
    RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (upperEndpoint c₀ R x ω)) (unequalRevealFiber s R x j ω₀) =
      expect (unequalEndpointParams s R x j ω₀).law.toPMF
        (fun q => f (unequalShift s c₀ R x j ω₀ + q.val + (prefixRows R x ω₀).card)) := by
  have hy (ω : Sample cuts) (hf : unequalRevealFiber s R x j ω₀ ω) :
      unequalRandomRows s R x j ω = unequalSampleRows s R x j ω₀ ∩
        residualAllowed (unequalExposedRows s R x j ω₀)
          (s.allowed (x.2.get j)) (ω (prefixColumn x j)) := by
    rw [unequalRandomRows_eq, (other_unequalRows s R x j hf.1).1,
      (other_unequalRows s R x j hf.1).2]
  constructor
  · trans RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (unequalShift s c₀ R x j ω₀ +
        ((unequalSampleRows s R x j ω₀ ∩ residualAllowed
          (unequalExposedRows s R x j ω₀) (s.allowed (x.2.get j))
          (ω (prefixColumn x j))).card : ℤ))) (unequalRevealFiber s R x j ω₀)
    · apply conditionalExpect_congr_on
      intro ω hf
      rw [(unequal_endpoint_shift s c₀ R x j ω).1,
        (unequalShift_eq_of_unequalReveal s c₀ R x j hf).1, hy ω hf]
    · exact partialRevealSourceExpect cuts (prefixColumn x j)
        (unequalExposedRows s R x j ω₀) (unequalSampleRows s R x j ω₀)
        (s.allowed (x.2.get j)) ω₀ (unequalSampleRows_subset s R x j ω₀)
        (fun q => f (unequalShift s c₀ R x j ω₀ + q))
  · trans RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (unequalShift s c₀ R x j ω₀ +
        ((unequalSampleRows s R x j ω₀ ∩ residualAllowed
          (unequalExposedRows s R x j ω₀) (s.allowed (x.2.get j))
          (ω (prefixColumn x j))).card : ℤ) + (prefixRows R x ω₀).card))
      (unequalRevealFiber s R x j ω₀)
    · apply conditionalExpect_congr_on
      intro ω hf
      rw [(unequal_endpoint_shift s c₀ R x j ω).2,
        (unequalShift_eq_of_unequalReveal s c₀ R x j hf).1,
        (unequalShift_eq_of_unequalReveal s c₀ R x j hf).2, hy ω hf]
    · exact partialRevealSourceExpect cuts (prefixColumn x j)
        (unequalExposedRows s R x j ω₀) (unequalSampleRows s R x j ω₀)
        (s.allowed (x.2.get j)) ω₀ (unequalSampleRows_subset s R x j ω₀)
        (fun q => f (unequalShift s c₀ R x j ω₀ + q + (prefixRows R x ω₀).card))

end RiffleUpperV2.Anchor
