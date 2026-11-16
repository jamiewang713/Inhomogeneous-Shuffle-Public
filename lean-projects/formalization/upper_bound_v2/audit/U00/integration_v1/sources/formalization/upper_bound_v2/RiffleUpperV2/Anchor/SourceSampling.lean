import RiffleUpperV2.Anchor.PartialReveal
import RiffleUpperV2.Anchor.HypergeometricSymmetry

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Anchor
open TimeProfile RiffleLowerV2.Thinning.Compat

/-- Source convention Hyp(marked, population, sample): B is the fixed sample
and the residual allowed positions supply the marked count. -/
def sourceSamplingParams {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j)
    (hB : B ⊆ Finset.univ \ A) : HypergeomParams :=
  swappedParams (samplingParams (Finset.univ \ A) B (residualMarked A D c₀) hB
    (residualMarked_le A D c₀))

@[simp] theorem sourceSamplingParams_population {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j)
    (hB : B ⊆ Finset.univ \ A) :
    (sourceSamplingParams A B D c₀ hB).population = n-A.card := by
  simp [sourceSamplingParams, swappedParams, samplingParams, Finset.card_sdiff_of_subset]

@[simp] theorem sourceSamplingParams_marked {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j)
    (hB : B ⊆ Finset.univ \ A) :
    (sourceSamplingParams A B D c₀ hB).marked =
      Hypergeometric.allowedCount cuts j D - (A.filter fun r => c₀.val r ∈ D).card := rfl

@[simp] theorem sourceSamplingParams_draws {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j)
    (hB : B ⊆ Finset.univ \ A) :
    (sourceSamplingParams A B D c₀ hB).draws = B.card := rfl

/-- All moments of the partial-reveal count have exactly the source's law. -/
theorem partialRevealSourceExpect {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (ω₀ : Sample cuts)
    (hB : B ⊆ Finset.univ \ A) (f : ℕ → ℝ) :
    RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => f (B ∩ residualAllowed A D (ω j)).card) (partialRevealFiber j A ω₀) =
    expect (sourceSamplingParams A B D (ω₀ j) hB).law.toPMF (fun q => f q.val) := by
  exact (partialRevealConditionalExpect cuts j A B D ω₀ hB f).trans
    (hypergeometricSwappedExpectPMF _ f)

/-- All events, including endpoint atoms after a proved revealed shift, transfer. -/
theorem partialRevealSourceProbability {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (ω₀ : Sample cuts)
    (hB : B ⊆ Finset.univ \ A) (E : ℕ → Prop) :
    RiffleLowerV2.conditionalProbability (fixedCountPMF cuts)
      (fun ω => E (B ∩ residualAllowed A D (ω j)).card) (partialRevealFiber j A ω₀) =
    probability (sourceSamplingParams A B D (ω₀ j) hB).law.toPMF (fun q => E q.val) := by
  exact (partialRevealConditionalProbability cuts j A B D ω₀ hB E).trans
    (hypergeometricSwappedProbability _ E)

/-- Exact centered second moment; no positive variance is required for the identity. -/
theorem partialRevealSourceVariance {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A B : Finset (Fin n)) (D : Finset (Fin k)) (ω₀ : Sample cuts)
    (hB : B ⊆ Finset.univ \ A) :
    RiffleLowerV2.conditionalExpect (fixedCountPMF cuts)
      (fun ω => ((B ∩ residualAllowed A D (ω j)).card -
        (sourceSamplingParams A B D (ω₀ j) hB).mean)^2) (partialRevealFiber j A ω₀) =
      (sourceSamplingParams A B D (ω₀ j) hB).varianceFormula := by
  exact (partialRevealSourceExpect cuts j A B D ω₀ hB
    (fun q => ((q : ℝ) - (sourceSamplingParams A B D (ω₀ j) hB).mean)^2)).trans
      (Hypergeometric.exactVariance _)

end RiffleUpperV2.Anchor
