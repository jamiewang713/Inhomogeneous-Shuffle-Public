import RiffleLowerV2.Occupancy.RegimeAlgebra
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RiffleLowerV2.Occupancy.rare_sandwich_error,
    ``RiffleLowerV2.Occupancy.rare_marginal_relative,
    ``RiffleLowerV2.Occupancy.rare_marginal_lower,
    ``RiffleLowerV2.Occupancy.rare_pair_relative,
    ``RiffleLowerV2.Occupancy.pair_relative_of_benchmark,
    ``RiffleLowerV2.Occupancy.abs_probability_covariance_le_complement]
  for name in names do
    let some info := env.find? name | throwError "Missing export {name}"
    unless info.isTheorem do throwError "Not a theorem {name}"
    let dependencies ← Lean.collectAxioms name
    for ax in dependencies do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected trusted closure at {name}: {ax}"
    let typ ← liftTermElabM <| Meta.ppExpr info.type
    let data := Json.mkObj [("name", toJson name.toString), ("type", toJson typ.pretty),
      ("axioms", toJson (dependencies.map Name.toString))]
    logInfo m!"LB08_REGIME_DECLARATION_JSON {data.compress}"
