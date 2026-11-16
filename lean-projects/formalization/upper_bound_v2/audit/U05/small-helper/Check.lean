import RiffleUpperV2.Conditional.SmallCylinderBounds
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
    if ["RiffleUpperV2.Conditional.PrefixAdapters", "RiffleUpperV2.Conditional.SmallCylinderBounds"].contains moduleName then
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
      logInfo m!"U05_SMALL_DECLARATION_JSON {row.compress}"
      count := count + 1
  logInfo m!"U05_SMALL_HELPER_TRUST_OK {count}"

set_option pp.fullNames true
set_option pp.universes true
#check @RiffleUpperV2.Conditional.inCylinder_iff_take
#print axioms RiffleUpperV2.Conditional.inCylinder_iff_take
#check @RiffleUpperV2.Conditional.inCylinder_exists
#print axioms RiffleUpperV2.Conditional.inCylinder_exists
#check @RiffleUpperV2.Conditional.prefixFirst_of_cylinder
#print axioms RiffleUpperV2.Conditional.prefixFirst_of_cylinder
#check @RiffleUpperV2.Conditional.tailBinPrefix_of_first
#print axioms RiffleUpperV2.Conditional.tailBinPrefix_of_first
#check @RiffleUpperV2.Conditional.tailBinPrefix_of_cylinder
#print axioms RiffleUpperV2.Conditional.tailBinPrefix_of_cylinder
#check @RiffleUpperV2.Conditional.inCylinder_tailBinPrefix
#print axioms RiffleUpperV2.Conditional.inCylinder_tailBinPrefix
#check @RiffleUpperV2.Conditional.tinyCylinder_count
#print axioms RiffleUpperV2.Conditional.tinyCylinder_count
#check @RiffleUpperV2.Conditional.intermediateCylinder_collisions
#print axioms RiffleUpperV2.Conditional.intermediateCylinder_collisions
