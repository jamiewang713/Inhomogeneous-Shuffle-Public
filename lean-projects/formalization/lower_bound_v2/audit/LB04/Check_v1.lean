import RiffleLowerV2.Ascent.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true
set_option maxHeartbeats 4000000

example : RiffleLowerV2.Targets.ComponentConcentration := RiffleLowerV2.Ascent.componentConcentration
example : RiffleLowerV2.Targets.ComponentExpectation := RiffleLowerV2.Ascent.componentExpectation
example : RiffleLowerV2.Targets.UniformScan := RiffleLowerV2.Ascent.uniformScan
example : RiffleLowerV2.Targets.ComponentComparison := RiffleLowerV2.Ascent.componentComparison
example : RiffleLowerV2.Targets.UniformGraphScan := RiffleLowerV2.Ascent.uniformGraphScan
example : RiffleLowerV2.Targets.RelativeOrderIndependence := RiffleLowerV2.Ascent.relativeOrderIndependence
example : RiffleLowerV2.Targets.BoundaryAscentProbability := RiffleLowerV2.Ascent.boundaryAscentProbability
example : RiffleLowerV2.Targets.BernoulliMGF := RiffleLowerV2.Ascent.bernoulliMGF
example : RiffleLowerV2.Targets.LeastSuccessfulTranslate := RiffleLowerV2.Ascent.leastSuccessfulTranslate
example : RiffleLowerV2.Targets.ComponentConcentrationTwoSided := RiffleLowerV2.Ascent.componentConcentrationTwoSided

#check RiffleLowerV2.Ascent.conditionalLalleyTest
#check RiffleLowerV2.Ascent.conditionalLalleyTendsto
#check RiffleLowerV2.Ascent.chosenTranslate_measurable

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RiffleLowerV2.Ascent." || label.startsWith "_private.RiffleLowerV2.Ascent." then
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
