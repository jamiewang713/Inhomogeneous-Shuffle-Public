import RiffleLowerV2.Occupancy.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option maxHeartbeats 4000000
set_option pp.universes false
set_option pp.funBinderTypes true

example : RiffleLowerV2.Targets.UniformOccupancy :=
  RiffleLowerV2.Occupancy.uniformOccupancy
example : RiffleLowerV2.Targets.ConditionalCollisionStability :=
  RiffleLowerV2.Occupancy.conditionalCollisionStability
example : RiffleLowerV2.Targets.CollisionChebyshev :=
  RiffleLowerV2.Occupancy.collisionChebyshev

#print RiffleLowerV2.Targets.UniformOccupancy
#print RiffleLowerV2.Targets.ConditionalCollisionStability
#print RiffleLowerV2.Targets.CollisionChebyshev

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RiffleLowerV2.Occupancy." ||
        label.startsWith "_private.RiffleLowerV2.Occupancy." then
      let dependencies ← Lean.collectAxioms name
      for ax in dependencies do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected trusted closure at {name}: {ax}"
      let typeDeps := info.type.getUsedConstants.map Name.toString
      let valueDeps := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants.map Name.toString
        | none => #[]
      let typ ← liftTermElabM <| Meta.ppExpr info.type
      let kind := if info.isTheorem then "theorem" else "definition-or-generated"
      let data := Json.mkObj [("name", toJson label), ("kind", toJson kind),
        ("type", toJson typ.pretty),
        ("type_dependencies", toJson typeDeps), ("value_dependencies", toJson valueDeps),
        ("axioms", toJson (dependencies.map Name.toString))]
      logInfo m!"LB08_DECLARATION_JSON {data.compress}"
  logInfo "LB08 AUDIT_OK"
