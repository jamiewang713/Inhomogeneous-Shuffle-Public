import RiffleLowerV2.EmpiricalLower.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true
set_option maxHeartbeats 2000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RiffleLowerV2.EmpiricalLower." || label.startsWith "_private.RiffleLowerV2.EmpiricalLower." then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom closure at {name}: {ax}"
      let typeDeps := info.type.getUsedConstants.map Name.toString
      let valueDeps := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants.map Name.toString
        | none => #[]
      let typ ← liftTermElabM <| Meta.ppExpr info.type
      let val ← match info.value? (allowOpaque := true) with
        | some value => do
            if info.isTheorem then pure "" else
              let v ← liftTermElabM <| Meta.ppExpr value
              pure v.pretty
        | none => pure ""
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | _ => "generated"
      let data := Json.mkObj [("name", toJson label), ("kind", toJson kind),
        ("type", toJson typ.pretty), ("value", toJson val),
        ("type_dependencies", toJson typeDeps), ("value_dependencies", toJson valueDeps),
        ("axioms", toJson (axioms.map Name.toString))]
      logInfo m!"DECLARATION_JSON {data.compress}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required := #[(`RiffleLowerV2.EmpiricalLower.finiteLargestWordTV, `RiffleLowerV2.Targets.FiniteLargestWordTV),
    (`RiffleLowerV2.EmpiricalLower.largestOnly, `RiffleLowerV2.Targets.LargestOnlyTarget),
    (`RiffleLowerV2.EmpiricalLower.manyEdges, `RiffleLowerV2.Targets.ManyEdgesTarget),
    (`RiffleLowerV2.EmpiricalLower.coldOnly, `RiffleLowerV2.Targets.ColdOnlyTarget),
    (`RiffleLowerV2.EmpiricalLower.empiricalCombined, `RiffleLowerV2.Targets.EmpiricalCombinedTarget)]
  for (name, target) in required do
    match env.find? name with
    | some info =>
        unless info.isTheorem do
          throwError "Required export {name} is not a theorem"
        unless info.type.isConstOf target do
          throwError "Required export {name} has changed type"
    | none => throwError "Required export {name} missing"
  Lean.logInfo "LB10_REQUIRED_THEOREMS_VERIFIED"

#check RiffleLowerV2.EmpiricalLower.finiteLargestWordTV
#check RiffleLowerV2.EmpiricalLower.largestOnly
#check RiffleLowerV2.EmpiricalLower.manyEdges
#check RiffleLowerV2.EmpiricalLower.coldOnly
#check RiffleLowerV2.EmpiricalLower.empiricalCombined
#print axioms RiffleLowerV2.EmpiricalLower.finiteLargestWordTV
#print axioms RiffleLowerV2.EmpiricalLower.largestOnly
#print axioms RiffleLowerV2.EmpiricalLower.manyEdges
#print axioms RiffleLowerV2.EmpiricalLower.coldOnly
#print axioms RiffleLowerV2.EmpiricalLower.empiricalCombined
