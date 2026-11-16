import RiffleLowerV2.Factorial.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option maxHeartbeats 4000000
set_option pp.universes false
set_option pp.funBinderTypes true

example : RiffleLowerV2.Targets.ExactJointFactorial := RiffleLowerV2.Factorial.exactJointFactorial
example : RiffleLowerV2.Targets.RelativeJointFactorial := RiffleLowerV2.Factorial.relativeJointFactorial
example : RiffleLowerV2.Targets.ResidualJointFactorial := RiffleLowerV2.Factorial.residualJointFactorial
example : RiffleLowerV2.Targets.ResidualRelativeFactorial := RiffleLowerV2.Factorial.residualRelativeFactorial
example : RiffleLowerV2.Targets.ResidualMeanComparison := RiffleLowerV2.Factorial.residualMeanComparison
example : RiffleLowerV2.Targets.BonferroniSandwich := RiffleLowerV2.Factorial.bonferroniSandwich
example : RiffleLowerV2.Targets.BonferroniProduct := RiffleLowerV2.Factorial.bonferroniProduct
example : RiffleLowerV2.Targets.CentralComparison := RiffleLowerV2.Factorial.centralComparison
example : RiffleLowerV2.Targets.CentralComparisonOne := RiffleLowerV2.Factorial.centralComparisonOne
example : RiffleLowerV2.Targets.RareSandwich := RiffleLowerV2.Factorial.rareSandwich

#check RiffleLowerV2.Factorial.conditional_wordCount_eq_residualWordMean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RiffleLowerV2.Factorial." || label.startsWith "_private.RiffleLowerV2.Factorial." then
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
