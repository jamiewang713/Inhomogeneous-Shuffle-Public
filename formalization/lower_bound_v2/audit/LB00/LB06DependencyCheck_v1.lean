import RiffleLowerV2
import RiffleTimeProfile.Analysis
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Stirling
import Lean.Util.CollectAxioms

set_option maxHeartbeats 2000000

#check TimeProfile.exists_regular_partition
#check Nat.multinomial
#check Nat.multinomial_spec
#check Stirling.log_stirlingSeq_formula
#check Stirling.log_stirlingSeq'_antitone
#check Stirling.log_stirlingSeq_bounded_by_constant
#check RiffleLowerV2.Targets.RoundedTypeTarget

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checkedModules : Array Name := #[`RiffleTimeProfile.Analysis, `Mathlib.Data.List.GetD, `Mathlib.Data.List.ToFinsupp, `Mathlib.Data.Nat.Choose.Multinomial, `Mathlib.Analysis.SumOverResidueClass, `Mathlib.Analysis.Asymptotics.SpecificAsymptotics, `Mathlib.Analysis.PSeries, `Mathlib.Analysis.Real.Pi.Wallis, `Mathlib.Analysis.SpecialFunctions.Stirling]
  let mut count := 0
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
