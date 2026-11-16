import RiffleUpperV2.Conditional.LargeFirstMoment
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
    if ["RiffleUpperV2.Conditional.LargeConcentration", "RiffleUpperV2.Conditional.LargeMargin", "RiffleUpperV2.Conditional.LargeFirstMoment"].contains moduleName then
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
      logInfo m!"U05_LARGE_DECLARATION_JSON {row.compress}"
      count := count + 1
  logInfo m!"U05_LARGE_HELPER_TRUST_OK {count}"

set_option pp.fullNames true
set_option pp.universes true
#check @RiffleUpperV2.Conditional.inducedCylinder_count
#print axioms RiffleUpperV2.Conditional.inducedCylinder_count
#check @RiffleUpperV2.Conditional.largeMean_error
#print axioms RiffleUpperV2.Conditional.largeMean_error
#check @RiffleUpperV2.Conditional.largeCylinder_concentration
#print axioms RiffleUpperV2.Conditional.largeCylinder_concentration
#check @RiffleUpperV2.Conditional.largeCylinder_sizeExponent
#print axioms RiffleUpperV2.Conditional.largeCylinder_sizeExponent
#check @RiffleUpperV2.Conditional.largeCylinder_errors
#print axioms RiffleUpperV2.Conditional.largeCylinder_errors
#check @RiffleUpperV2.Conditional.largeCylinder_preservation
#print axioms RiffleUpperV2.Conditional.largeCylinder_preservation
#check @RiffleUpperV2.Conditional.largeCylinder_firstMoment
#print axioms RiffleUpperV2.Conditional.largeCylinder_firstMoment
