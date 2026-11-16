import RiffleLowerV2.Thinning.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option maxHeartbeats 4000000
set_option pp.universes false
set_option pp.funBinderTypes true

example : RiffleLowerV2.Targets.SuccessiveThinning := RiffleLowerV2.Thinning.successiveThinning
example : RiffleLowerV2.Targets.PrefixTails := RiffleLowerV2.Thinning.prefixTails
example : RiffleLowerV2.Targets.AllPrefixConcentration := RiffleLowerV2.Thinning.allPrefixConcentration
example : RiffleLowerV2.Targets.PrefixFailureUniform := RiffleLowerV2.Thinning.prefixFailureUniform
example : RiffleLowerV2.Targets.ResidualLaw := RiffleLowerV2.Thinning.residualLaw
example : RiffleLowerV2.Targets.HypergeometricTransform := RiffleLowerV2.Thinning.hypergeometricTransform
example : RiffleLowerV2.Targets.MaximalMeanIdentity := RiffleLowerV2.Thinning.maximalMeanIdentity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RiffleLowerV2.Thinning." ||
        label.startsWith "_private.RiffleLowerV2.Thinning." then
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
      logInfo m!"LB02_DECLARATION_JSON {data.compress}"
