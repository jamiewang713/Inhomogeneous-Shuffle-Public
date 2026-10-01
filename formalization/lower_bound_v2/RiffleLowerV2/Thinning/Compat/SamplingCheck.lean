import RiffleLowerV2.Thinning.Sampling
import RiffleLowerV2.Thinning.ColumnSampling
import Lean.Util.CollectAxioms

#check (RiffleLowerV2.Thinning.hypergeometricTransform :
  RiffleLowerV2.Targets.HypergeometricTransform)

set_option maxHeartbeats 2000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[``RiffleLowerV2.Thinning.permutation_subset_expect,
      ``RiffleLowerV2.Thinning.permutation_intersection_transform,
      ``RiffleLowerV2.Thinning.hypergeometricTransform,
      ``RiffleLowerV2.Thinning.columnRelabelEquiv,
      ``RiffleLowerV2.Thinning.column_subset_expect,
      ``RiffleLowerV2.Thinning.column_intersection_transform] do
    let some info := env.find? name | throwError "Missing checked declaration {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected dependency closure at {name}: {ax}"
    let typ ← liftTermElabM <| Meta.ppExpr info.type
    let data := Json.mkObj [("name", toJson name.toString), ("type", toJson typ.pretty),
      ("is_theorem", toJson info.isTheorem),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"SAMPLING_DECLARATION_JSON {data.compress}"
