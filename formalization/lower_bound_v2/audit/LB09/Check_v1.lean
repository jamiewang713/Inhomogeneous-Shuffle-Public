import RiffleLowerV2.Localization.Main
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
    if label.startsWith "RiffleLowerV2.Localization." || label.startsWith "_private.RiffleLowerV2.Localization." then
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
  let required := #[(`RiffleLowerV2.Localization.relativeEndpoint, `RiffleLowerV2.Targets.RelativeEndpointTarget),
    (`RiffleLowerV2.Localization.deterministicColdGeometry, `RiffleLowerV2.Targets.DeterministicColdGeometryTarget),
    (`RiffleLowerV2.Localization.localization, `RiffleLowerV2.Targets.LocalizationTarget),
    (`RiffleLowerV2.Localization.coldGeometryFromEmpirical, `RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget),
    (`RiffleLowerV2.Localization.lB09, `RiffleLowerV2.Targets.LB09Target)]
  for (name, target) in required do
    match env.find? name with
    | some info =>
        unless info.isTheorem do
          throwError "Required export {name} is not a theorem"
        unless info.type.isConstOf target do
          throwError "Required export {name} has changed type"
    | none => throwError "Required export {name} missing"
  Lean.logInfo "LB09_REQUIRED_THEOREMS_VERIFIED"

#check RiffleLowerV2.Localization.relativeEndpoint
#check RiffleLowerV2.Localization.deterministicColdGeometry
#check RiffleLowerV2.Localization.localization
#check RiffleLowerV2.Localization.coldGeometryFromEmpirical
#check RiffleLowerV2.Localization.lB09
#print axioms RiffleLowerV2.Localization.relativeEndpoint
#print axioms RiffleLowerV2.Localization.deterministicColdGeometry
#print axioms RiffleLowerV2.Localization.localization
#print axioms RiffleLowerV2.Localization.coldGeometryFromEmpirical
#print axioms RiffleLowerV2.Localization.lB09
