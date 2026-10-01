import RiffleLowerV2
import RiffleLowerV2.Model.GraphSorting
import RiffleLowerV2.Model.FiniteLaws
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Lean.Util.CollectAxioms

set_option maxHeartbeats 2000000

#check ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
#check ProbabilityTheory.HasSubgaussianMGF.mgf_le
#check RiffleLowerV2.Model.componentIndex_monotone
#check RiffleLowerV2.Model.componentIndex_lt_of_missing
#check RiffleLowerV2.Model.sort_pair_preserves_first
#check RiffleLowerV2.Model.componentSort_preserves_component
#check RiffleLowerV2.Model.componentSort_increasing
#check RiffleLowerV2.Model.expect_uniform
#check RiffleLowerV2.Model.uniform_expect_equiv
#check RiffleLowerV2.Model.map_uniform_equiv
#check RiffleLowerV2.expect_eq_integral

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checkedModules : Array Name := #[`Mathlib.MeasureTheory.Measure.Tilted, `Mathlib.Probability.Moments.Tilted, `Mathlib.Probability.Moments.SubGaussian, `Mathlib.Probability.ProbabilityMassFunction.Integrals, `RiffleLowerV2.Model.GraphSorting, `RiffleLowerV2.Model.FiniteLaws]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.allImportedModuleNames[idx]!
      if checkedModules.contains mod then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom closure at {name}: {ax}"
        let typ ← liftTermElabM <| Meta.ppExpr info.type
        let data := Json.mkObj [("name", toJson name.toString),
          ("module", toJson mod.toString), ("type", toJson typ.pretty),
          ("is_theorem", toJson info.isTheorem),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"DEPENDENCY_DECLARATION_JSON {data.compress}"
        count := count + 1
  unless count > 0 do throwError "No dependency declarations audited"
  logInfo m!"DEPENDENCY_AXIOMS_OK {count}"
