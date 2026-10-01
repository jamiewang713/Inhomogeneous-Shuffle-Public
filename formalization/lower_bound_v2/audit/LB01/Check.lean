import RiffleLowerV2.Model.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true
set_option maxHeartbeats 2000000


example : RiffleLowerV2.Targets.ColumnIndependence := RiffleLowerV2.Model.columnIndependence
example : RiffleLowerV2.Targets.RowRelabeling := RiffleLowerV2.Model.rowRelabeling
example : RiffleLowerV2.Targets.StableTie := RiffleLowerV2.Model.stableTie
example : RiffleLowerV2.Targets.PrefixRanks := RiffleLowerV2.Model.prefixRanks
example : RiffleLowerV2.Targets.GraphRepresentation := RiffleLowerV2.Model.graphRepresentation
example : RiffleLowerV2.Targets.GraphEventIdentity := RiffleLowerV2.Model.graphEventIdentity
example : RiffleLowerV2.Targets.PhysicalMatrixBridge := RiffleLowerV2.Model.physicalMatrixBridge
example : RiffleLowerV2.Targets.InversionTV := RiffleLowerV2.Model.inversionTV

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RiffleLowerV2.Model." || label.startsWith "_private.RiffleLowerV2.Model." then
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
