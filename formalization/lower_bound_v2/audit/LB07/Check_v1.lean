import RiffleLowerV2.ProfileTransfer.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true
set_option maxHeartbeats 2000000

example : RiffleLowerV2.Targets.GenericQuadrature :=
  RiffleLowerV2.ProfileTransfer.genericQuadrature
example : RiffleLowerV2.Targets.JointPsiContinuity :=
  RiffleLowerV2.ProfileTransfer.jointPsiContinuity
example : RiffleLowerV2.Targets.MarginTransferTarget :=
  RiffleLowerV2.ProfileTransfer.marginTransfer
example : RiffleLowerV2.Targets.ProfileTransferTarget :=
  RiffleLowerV2.ProfileTransfer.profileTransfer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RiffleLowerV2.ProfileTransfer." ||
        label.startsWith "_private.RiffleLowerV2.ProfileTransfer." then
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom closure at {name}: {ax}"
      let typeDeps := info.type.getUsedConstants.map Name.toString
      let valueDeps := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants.map Name.toString
        | none => #[]
      let typ ← liftTermElabM <| Meta.ppExpr info.type
      let kind := if info.isTheorem then "theorem" else "definition-or-generated"
      let data := Json.mkObj [("name", toJson label), ("kind", toJson kind),
        ("type", toJson typ.pretty), ("type_dependencies", toJson typeDeps),
        ("value_dependencies", toJson valueDeps), ("axioms", toJson (axs.map Name.toString))]
      logInfo m!"DECLARATION_JSON {data.compress}"

#print RiffleLowerV2.Targets.GenericQuadrature
#print RiffleLowerV2.Targets.JointPsiContinuity
#print RiffleLowerV2.Targets.MarginTransferTarget
#print RiffleLowerV2.Targets.ProfileTransferTarget
