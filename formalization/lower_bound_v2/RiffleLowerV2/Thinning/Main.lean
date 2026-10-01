import RiffleLowerV2.Thinning.Process
import RiffleLowerV2.Thinning.Prefixes
import RiffleLowerV2.Thinning.Residual.Prefix
import RiffleLowerV2.Thinning.Residual.Independence
import RiffleLowerV2.Thinning.UniformError

noncomputable section
namespace RiffleLowerV2.Thinning
open TimeProfile

/-- The concrete conditional residual transform, with every generic input
supplied by the proved prefix theorem. -/
theorem residualPrefixTransform {N k K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (hb : b < N) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r))
    (w : Prefix k K) (s : ℝ) (hs : 0 < s) :
    conditionalExpect (fixedCountPMF cuts) (fun ω => s ^ residualPrefixCount r w ω)
      (prescriptionEvent r) ≤ (1-residualPrefixMass cuts r w+residualPrefixMass cuts r w*s)^(N-b) ∧
    (1-residualPrefixMass cuts r w+residualPrefixMass cuts r w*s)^(N-b) ≤
      Real.exp (residualPrefixMean cuts r w*(s-1)) :=
  residualPrefixTransform_of_prefixTransform prefixTransform cuts r hb hr hp w s hs

/-- Concrete conditional residual tails with the reduced population and mean.
The deterministic prefix and admissible prescription are uniformly quantified. -/
theorem residualPrefixTails {N k K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (hb : b < N) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r)) (w : Prefix k K) :
    (∀ t : ℝ, 0 < t →
      conditionalProbability (fixedCountPMF cuts)
        (fun ω => t ≤ |(residualPrefixCount r w ω : ℝ) - residualPrefixMean cuts r w|)
        (prescriptionEvent r) ≤
      2 * Real.exp (-t^2 / (4 * (residualPrefixMean cuts r w + t)))) ∧
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => (residualPrefixCount r w ω : ℝ) ≤ residualPrefixMean cuts r w / 2)
      (prescriptionEvent r) ≤ Real.exp (-chernoffConstant * residualPrefixMean cuts r w) ∧
    conditionalProbability (fixedCountPMF cuts) (fun ω => residualPrefixCount r w ω < 2)
      (prescriptionEvent r) ≤ 2 * Real.exp (-residualPrefixMean cuts r w / 2) :=
  residualPrefixTails_of_prefixTails prefixTails cuts r hb hr hp w

end RiffleLowerV2.Thinning
