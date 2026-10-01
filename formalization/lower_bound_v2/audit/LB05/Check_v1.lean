import RiffleLowerV2.Witness.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true
set_option maxHeartbeats 2000000

example : RiffleLowerV2.Targets.OneColumnTiltTarget := RiffleLowerV2.Witness.oneColumnTilt
example : RiffleLowerV2.Targets.EmpiricalTiltTarget := RiffleLowerV2.Witness.empiricalTilt
example : RiffleLowerV2.Targets.ColdWitnessTarget := RiffleLowerV2.Witness.coldWitness
example : RiffleLowerV2.Targets.LB05Target := RiffleLowerV2.Witness.lB05

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RiffleLowerV2.Witness." ||
        label.startsWith "_private.RiffleLowerV2.Witness." then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom closure at {name}: {ax}"
      let typeDeps := info.type.getUsedConstants.map Name.toString
      let valueDeps := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants.map Name.toString
        | none => #[]
      let typ ← liftTermElabM <| Meta.ppExpr info.type
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | _ => "generated"
      let data := Json.mkObj [("name", toJson label), ("kind", toJson kind),
        ("type", toJson typ.pretty), ("type_dependencies", toJson typeDeps),
        ("value_dependencies", toJson valueDeps),
        ("axioms", toJson (axioms.map Name.toString))]
      logInfo m!"DECLARATION_JSON {data.compress}"

#print axioms RiffleLowerV2.Witness.oneColumnTilt
#print axioms RiffleLowerV2.Witness.empiricalTilt
#print axioms RiffleLowerV2.Witness.coldWitness
#print axioms RiffleLowerV2.Witness.lB05
