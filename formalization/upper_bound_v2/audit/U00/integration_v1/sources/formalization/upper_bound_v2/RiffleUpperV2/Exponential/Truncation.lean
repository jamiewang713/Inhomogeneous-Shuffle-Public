import RiffleUpperV2.Exponential.Numerical
import RiffleUpperV2.GraphOverlap.LargestComponent

noncomputable section
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exponential
open RiffleLowerV2.Thinning

/-- A truncation event on one matrix, intersecting regularity and its actual graph bound. -/
def regularTruncation {k N K : ℕ} (cuts : Cuts k N K)
    (R : Sample cuts → Prop) (bound : ℕ) (ω : Sample cuts) : Prop :=
  R ω ∧ GraphOverlap.BoundedComponents (shuffleEdges ω) bound

/-- Source bounded-component truncation: the exceptional regularity probability is charged once. -/
theorem boundedComponentTruncation {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 2 ≤ N) (R : Sample cuts → Prop) (bound : ℕ) (hbound : 2 ≤ bound)
    {η A : ℝ} (hmean : RiffleLowerV2.maximalMean cuts (by omega) ≤ (N : ℝ)^(-η))
    (hexp : A+1 ≤ η*bound) :
    probability (fixedCountPMF cuts) (fun ω => ¬ regularTruncation cuts R bound ω) ≤
      probability (fixedCountPMF cuts) (fun ω => ¬ R ω) + (N : ℝ)^(-A)/(bound+1).factorial := by
  have hsub : ∀ ω : Sample cuts, ¬ regularTruncation cuts R bound ω →
      ¬ R ω ∨ ¬ GraphOverlap.BoundedComponents (shuffleEdges ω) bound := by
    intro ω hω
    by_cases hr : R ω
    · exact Or.inr (fun hc => hω ⟨hr, hc⟩)
    · exact Or.inl hr
  have hu := probability_union_le (fixedCountPMF cuts) (fun ω => ¬ R ω)
    (fun ω => ¬ GraphOverlap.BoundedComponents (shuffleEdges ω) bound)
  have ht := GraphOverlap.boundedComponentTail cuts hN hbound hmean hexp
  have hs := probability_mono (fixedCountPMF cuts) hsub
  exact hs.trans (hu.trans (by linarith))

/-- Quantitative bounded-component corollary with the geometric denominator at least 1/2.
The empirical lane constructs the regularity event, conditional bounds, and directional cover. -/
theorem boundedComponentExplorationTV {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 2 ≤ N) (R : Sample cuts → Prop) (bound : ℕ) (hbound : 2 ≤ bound)
    {η A : ℝ} (hmean : RiffleLowerV2.maximalMean cuts (by omega) ≤ (N : ℝ)^(-η))
    (hexp : A+1 ≤ η*bound)
    (d : ℕ) (hd : 0 < d) (H : Fin d → Type*) [∀ a, Fintype (H a)]
    (h : ∀ a, ℕ → (Sample cuts × Sample cuts) → H a)
    (X : Fin d → ℕ → (Sample cuts × Sample cuts) → ℕ)
    (B : Fin d → ℕ → (Sample cuts × Sample cuts) → Prop) (m : Fin d → ℕ)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (href : ∀ a, Refining (h a) (m a))
    (hunit : ∀ a ω, UnitIncrements (fun i => X a i ω) (m a))
    (hzero : ∀ a ω, X a 0 ω = 0)
    (had : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (X a i))
    (hB : ∀ a i, i ≤ m a → HistoryMeasurable (h a i) (B a i))
    (htail : ∀ a i, i < m a → ∀ v, B a i v →
      0 < probability (independentPairLaw cuts) (fun ω => h a i ω = h a i v) →
      conditionalExpect (independentPairLaw cuts)
        (fun ω => (X a (m a) ω - X a i ω : ℕ)) (fun ω => h a i ω = h a i v) ≤ γ)
    (hC : ∀ ω : Sample cuts × Sample cuts,
      regularTruncation cuts R bound ω.1 ∧ regularTruncation cuts R bound ω.2 →
      ∀ a, goodPrefix (B a) (m a) ω)
    (hcover : ∀ ω : Sample cuts × Sample cuts,
      regularTruncation cuts R bound ω.1 ∧ regularTruncation cuts R bound ω.2 →
      (shuffleEdges ω.1 ∩ shuffleEdges ω.2).card ≤ ∑ a, X a (m a) ω)
    (hsmall : ((componentConstant bound)^d - 1)*γ ≤ 1/2) :
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤
      Real.sqrt (2*((componentConstant bound)^d - 1)*γ) / 2 +
      probability (fixedCountPMF cuts) (fun ω => ¬ R ω) +
      (N : ℝ)^(-A)/(bound+1).factorial := by
  have hq : 0 ≤ (componentConstant bound)^d - 1 := by
    have hh : (1 : ℝ) ≤ (componentConstant bound)^d := one_le_pow₀ (componentConstant_ge_one bound)
    linarith
  have htv := finiteExplorationTV cuts (regularTruncation cuts R bound) bound hbound
    (fun _ hω => hω.2) d hd H h X B m γ hγ href hunit hzero had hB htail hC hcover
    (by linarith)
  have ht := boundedComponentTruncation cuts hN R bound hbound hmean hexp
  have hs := Real.sqrt_le_sqrt (geometric_ratio_le_twice hq hγ hsmall)
  linarith

end RiffleUpperV2.Exponential
