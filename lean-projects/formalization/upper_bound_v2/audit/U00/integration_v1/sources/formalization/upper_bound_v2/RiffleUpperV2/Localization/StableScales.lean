import RiffleUpperV2.Localization.Stopping
import RiffleUpperV2.Anchor.Scales

noncomputable section
namespace RiffleUpperV2.Localization
open Anchor

/-- Concrete anchored version of eq:ub-anchored-fluctuation-comparison. -/
theorem anchoredFluctuationComparison {k n d : ℕ} (N : ℕ) (hN : 1 < N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    {χ : ℝ} {y z v : Prefix k d} (hpair : GenuineBoundaryPair cuts R χ y z v) :
    meanExponent N cuts R v - crossingPenalty N χ ≤ 2 * boundaryFluctuation N cuts R v :=
  fluctuationComparison hN hpair.legal_join hpair.chi_pos
    (genuine_sideScale_pos cuts hn R hpair).2

/-- Concrete source eq:ub-proper-fluctuation-lower, with the finite-N correction. -/
theorem properStableFluctuationLower {k n d : ℕ} (N : ℕ) (hN : 1 < N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    {χ δ : ℝ} {y z v x : Prefix k d} (hpair : GenuineBoundaryPair cuts R χ y z v)
    (hx : ProperStable N cuts R v δ x) :
    δ - crossingPenalty N χ ≤ boundaryFluctuation N cuts R v := by
  apply properFluctuationLower (anchoredFluctuationComparison N hN cuts hn R hpair)
  have h := proper_join_not_stopped hx
  exact le_of_not_gt h

theorem properStableFluctuationPositive {k n d : ℕ} (N : ℕ) (hN : 1 < N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    {χ δ : ℝ} {y z v x : Prefix k d} (hpair : GenuineBoundaryPair cuts R χ y z v)
    (hx : ProperStable N cuts R v δ x) (hq : crossingPenalty N χ ≤ δ/2) :
    δ/2 ≤ boundaryFluctuation N cuts R v := by
  have h := properStableFluctuationLower N hN cuts hn R hpair hx
  linarith

/-- Applies also to a large immediate-stop join; no properness hypothesis appears. -/
theorem large_stopped_fluctuation {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {v x : Prefix k d} {δ : ℝ}
    (hx : Stops N cuts R v δ x) (hlarge : 2*δ ≤ meanExponent N cuts R x) :
    δ < boundaryFluctuation N cuts R v := largeStableFluctuation hlarge hx

end RiffleUpperV2.Localization
