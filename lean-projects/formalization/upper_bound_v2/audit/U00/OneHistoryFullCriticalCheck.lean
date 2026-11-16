import RiffleUpperV2.Conditional.OneHistory
import RiffleUpperV2.ProfileUpper.Critical
import RiffleUpperV2.ProfileUpper.FullCritical
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
    if moduleName.startsWith "RiffleUpperV2.Conditional" || moduleName.startsWith "RiffleUpperV2.ProfileUpper" then
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
  logInfo m!"UPPER_ONE_HISTORY_FULL_CRITICAL_TRUST_OK {count}"
