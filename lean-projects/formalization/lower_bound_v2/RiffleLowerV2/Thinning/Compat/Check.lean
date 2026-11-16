import RiffleLowerV2.Thinning.Compat.SubsetTransform
import Lean.Util.CollectAxioms

set_option maxHeartbeats 2000000
set_option pp.universes false

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RiffleLowerV2.Thinning.Compat." ||
        label.startsWith "_private.RiffleLowerV2.Thinning.Compat." then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected dependency closure at {name}: {ax}"
      let typ ← liftTermElabM <| Meta.ppExpr info.type
      let data := Json.mkObj [("name", toJson label), ("type", toJson typ.pretty),
        ("is_theorem", toJson info.isTheorem),
        ("axioms", toJson (axioms.map Name.toString))]
      logInfo m!"COMPAT_DECLARATION_JSON {data.compress}"
