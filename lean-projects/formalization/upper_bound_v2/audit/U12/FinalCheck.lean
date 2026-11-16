import RiffleUpperV2.ProfileUpper.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

-- Incremental trust/type inventory, adapted from the immutable lower-bound
-- audit/LB12/generate_check_v5.py. No endpoint completion assertions here.
set_option maxHeartbeats 0
set_option pp.funBinderTypes true
set_option pp.universes false
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.allImportedModuleNames[idx]!.toString
      | none => ""
    if moduleName.startsWith "RiffleUpperV2.ProfileUpper" then
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom {ax} in {name}"
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .opaqueInfo _ => "opaque"
        | _ => "generated"
      if kind == "axiom" then throwError "Project axiom {name}"
      let ty ← liftTermElabM <| Meta.ppExpr ci.type
      let row := Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName),
        ("kind", toJson kind), ("type", toJson ty.pretty),
        ("all_direct_dependencies", toJson (ci.getUsedConstantsAsSet.toArray.map Name.toString)),
        ("axioms", toJson (axs.map Name.toString))]
      logInfo m!"UPPER_DECLARATION_JSON {row.compress}"
      count := count + 1
  logInfo m!"U12_FINAL_TRUST_OK {count}"

noncomputable section
open Set Filter
open scoped ENNReal
namespace RiffleUpperV2.ProfileUpper.Audit
open TimeProfile

theorem bufferedUpper_expanded :
  ∀ k : ℕ, 2 ≤ k → ∀ T η : ℝ, 0 < T → 0 < η →
  ∃ χ0 : ℝ, 0 < χ0 ∧ ∀ χ : ℝ, 0 < χ → χ ≤ χ0 →
  ∀ P : BorelPartition k, P.IsRegular χ (regularityConstant k) →
  ∀ g γ : ℝ, 0 < g → g < 1/(k : ℝ) → 0 < γ →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∃ φ0 : ℝ, 0 < φ0 ∧ ∀ φ : ℝ, 0 < φ → φ ≤ φ0 →
  ∀ μ : TimeLaw k, ScalarIntegrable μ P T → reducedMargin μ T ≤ -η →
  ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
  ∀ (N : ℕ) (hN : N0 ≤ N) (cuts : Cuts k N (horizonDepth N T)),
    AlmostLike cuts (by omega) μ P T ρ φ →
    LocalGood cuts (by omega) g γ ρ 0 T →
    tv (physicalInverseLaw cuts) (uniformPermutation N) ≤ ε :=
  bufferedUpper

theorem criticalTimeUpper_expanded :
  ∀ k : ℕ, 2 ≤ k → ∀ (μ : TimeLaw k) (cuts : ∀ N : ℕ, InfiniteCuts k N),
  ArbitrarilyFineApproximation μ cuts →
  (∀ t : ℝ, 0 ≤ t → criticalTime μ < ENNReal.ofReal t →
    Tendsto (fun N => tv (physicalInverseLaw ((cuts N).take (horizonDepth N t)))
      (uniformPermutation N)) atTop (nhds 0)) ∧
  (∀ ε : ℝ, 0 < ε → ε < 1 →
    limsup (fun N => mixingTime (cuts N) ε / ENNReal.ofReal (Real.log (N : ℝ))) atTop
      ≤ criticalTime μ) :=
  criticalTimeUpper

theorem randomEmpiricalBound_expanded :
  ∀ k : ℕ, 2 ≤ k → ∀ T η0 g0 γ0 : ℝ,
  0 < T → 0 < η0 → 0 < g0 → 0 < γ0 →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0,
  ∀ (N : ℕ) (hN : N0 ≤ N) (K : ℕ), (K : ℝ) ≤ T * Real.log (N : ℝ) →
  ∀ Q : PMF (Cuts k N K),
    tv (randomInverseLaw Q) (uniformPermutation N) ≤
      probability Q (fun cuts => ¬(EmpiricalNegativeMargin N 0 cuts (by omega) η0 ∧
        LocalGood cuts (by omega) g0 γ0 ρ 0 ((K : ℝ) / Real.log (N : ℝ)))) +
      (N : ℝ)^(-c) :=
  randomEmpiricalBound

theorem randomEmpiricalUpper_expanded :
  ∀ k : ℕ, 2 ≤ k → ∀ T η0 g0 γ0 : ℝ,
  0 < T → 0 < η0 → 0 < g0 → 0 < γ0 →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∀ (K : ℕ → ℕ), (∀ N, 2 ≤ N → (K N : ℝ) ≤ T * Real.log (N : ℝ)) →
  ∀ (Q : ∀ N, PMF (Cuts k N (K N))),
    Tendsto (fun N => probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N,
      EmpiricalNegativeMargin N 0 cuts (by omega) η0 ∧
      LocalGood cuts (by omega) g0 γ0 ρ 0 ((K N : ℝ) / Real.log (N : ℝ))))
      atTop (nhds 1) →
    Tendsto (fun N => tv (randomInverseLaw (Q N)) (uniformPermutation N)) atTop (nhds 0) :=
  randomEmpiricalUpper

theorem randomProfileUpper_expanded :
  ∀ k : ℕ, 2 ≤ k → ∀ T η : ℝ, 0 < T → 0 < η →
  ∃ χ0 : ℝ, 0 < χ0 ∧ ∀ χ : ℝ, 0 < χ → χ ≤ χ0 →
  ∀ P : BorelPartition k, P.IsRegular χ (regularityConstant k) →
  ∀ g γ : ℝ, 0 < g → g < 1/(k : ℝ) → 0 < γ →
  ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
  ∃ φ0 : ℝ, 0 < φ0 ∧ ∀ φ : ℝ, 0 < φ → φ ≤ φ0 →
  ∀ μ : TimeLaw k, ScalarIntegrable μ P T → reducedMargin μ T ≤ -η →
  ∀ Q : ∀ N, PMF (Cuts k N (horizonDepth N T)),
    Tendsto (fun N => probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N, AlmostLike cuts (by omega) μ P T ρ φ)) atTop (nhds 1) →
    Tendsto (fun N => probability (Q N) (fun cuts =>
      ∃ hN : 2 ≤ N, LocalGood cuts (by omega) g γ ρ 0 T)) atTop (nhds 1) →
    Tendsto (fun N => tv (randomInverseLaw (Q N)) (uniformPermutation N)) atTop (nhds 0) :=
  randomProfileUpper

end RiffleUpperV2.ProfileUpper.Audit

#check (RiffleUpperV2.ProfileUpper.bufferedUpper : RiffleUpperV2.Contracts.V1.P)
#print RiffleUpperV2.ProfileUpper.Audit.bufferedUpper_expanded
#print axioms RiffleUpperV2.ProfileUpper.bufferedUpper
#check (RiffleUpperV2.ProfileUpper.criticalTimeUpper : RiffleUpperV2.Contracts.V1.T)
#print RiffleUpperV2.ProfileUpper.Audit.criticalTimeUpper_expanded
#print axioms RiffleUpperV2.ProfileUpper.criticalTimeUpper
#check (RiffleUpperV2.ProfileUpper.randomEmpiricalBound : RiffleUpperV2.Contracts.V1.REmpiricalBound)
#print RiffleUpperV2.ProfileUpper.Audit.randomEmpiricalBound_expanded
#print axioms RiffleUpperV2.ProfileUpper.randomEmpiricalBound
#check (RiffleUpperV2.ProfileUpper.randomEmpiricalUpper : RiffleUpperV2.Contracts.V1.REmpirical)
#print RiffleUpperV2.ProfileUpper.Audit.randomEmpiricalUpper_expanded
#print axioms RiffleUpperV2.ProfileUpper.randomEmpiricalUpper
#check (RiffleUpperV2.ProfileUpper.randomProfileUpper : RiffleUpperV2.Contracts.V1.RProfile)
#print RiffleUpperV2.ProfileUpper.Audit.randomProfileUpper_expanded
#print axioms RiffleUpperV2.ProfileUpper.randomProfileUpper
#print RiffleUpperV2.ProfileUpper.criticalHorizonUpper
#print axioms RiffleUpperV2.ProfileUpper.criticalHorizonUpper
#print RiffleUpperV2.ProfileUpper.mixingTimeUpper
#print axioms RiffleUpperV2.ProfileUpper.mixingTimeUpper
#print RiffleUpperV2.ProfileUpper.fullCriticalTimeUpper
#print axioms RiffleUpperV2.ProfileUpper.fullCriticalTimeUpper
#print RiffleUpperV2.ProfileUpper.randomUpper
#print axioms RiffleUpperV2.ProfileUpper.randomUpper

#print axioms RiffleUpperV2.EmpiricalUpper.empiricalUpper
#print axioms RiffleUpperV2.Conditional.remainingCommonEdges
#print axioms RiffleUpperV2.FirstMoment.empiricalFirstMoment
