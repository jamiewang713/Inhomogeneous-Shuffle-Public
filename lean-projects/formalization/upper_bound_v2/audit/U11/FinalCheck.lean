import RiffleUpperV2.EmpiricalUpper.Main
import Lean

noncomputable section
namespace RiffleUpperV2.EmpiricalUpper.Audit

/-- Literal expansion of the frozen endpoint, with no additional hypothesis. -/
theorem empiricalUpper_expanded :
    ∀ (k : ℕ), 2 ≤ k → ∀ (T η0 g0 γ0 : ℝ),
    0 < T → 0 < η0 → 0 < g0 → 0 < γ0 →
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
    ∀ (N : ℕ) (hN : N0 ≤ N) (K : ℕ), (K : ℝ) ≤ T * Real.log (N : ℝ) →
    ∀ cuts : Cuts k N K,
      EmpiricalNegativeMargin N 0 cuts (by omega) η0 →
      LocalGood cuts (by omega) g0 γ0 ρ 0 ((K : ℝ) / Real.log (N : ℝ)) →
      tv (physicalInverseLaw cuts) (uniformPermutation N) ≤ (N : ℝ) ^ (-c) :=
  empiricalUpper

end RiffleUpperV2.EmpiricalUpper.Audit

#check (RiffleUpperV2.EmpiricalUpper.empiricalUpper : RiffleUpperV2.Contracts.V1.E)
#print RiffleUpperV2.EmpiricalUpper.Audit.empiricalUpper_expanded
#print axioms RiffleUpperV2.EmpiricalUpper.empiricalUpper
#print axioms RiffleUpperV2.EmpiricalUpper.deletedPrefixTVContraction
#print axioms RiffleUpperV2.EmpiricalUpper.restartHypotheses
#print axioms RiffleUpperV2.EmpiricalUpper.concreteExplorationTV
#print axioms RiffleUpperV2.Conditional.remainingCommonEdges
#print axioms RiffleUpperV2.FirstMoment.empiricalFirstMoment

open Lean Elab Command in
run_cmd do
  let targets := #[``RiffleUpperV2.EmpiricalUpper.empiricalUpper,
    ``RiffleUpperV2.EmpiricalUpper.deletedPrefixTVContraction,
    ``RiffleUpperV2.EmpiricalUpper.restartHypotheses,
    ``RiffleUpperV2.EmpiricalUpper.concreteExplorationTV,
    ``RiffleUpperV2.EmpiricalUpper.criterion_polynomial,
    ``RiffleUpperV2.Conditional.remainingCommonEdges,
    ``RiffleUpperV2.FirstMoment.empiricalFirstMoment]
  let mut rows : Array Json := #[]
  for name in targets do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    let info ← getConstInfo name
    unless info matches .thmInfo _ do
      throwError "Endpoint/helper {name} is not a theorem"
    rows := rows.push <| Json.mkObj [("name",toJson name.toString),
      ("axioms",toJson (axioms.map Name.toString)),("kernel_theorem",toJson true)]
  liftIO <| IO.FS.writeFile "audit/U11/final-trust.json" (toString <| toJson rows)
