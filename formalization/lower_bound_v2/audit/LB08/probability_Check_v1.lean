import RiffleLowerV2.Occupancy.Covariance
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true

#check RiffleLowerV2.Occupancy.variance_eventCount
#check RiffleLowerV2.Occupancy.variance_eventCount_le
#check RiffleLowerV2.Occupancy.variance_collisionCount_le
#check RiffleLowerV2.Occupancy.chebyshev_of_variance_le
#check RiffleLowerV2.Occupancy.lower_tail_success
#check RiffleLowerV2.Occupancy.positive_success

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RiffleLowerV2.Occupancy.probability_congr,
    ``RiffleLowerV2.Occupancy.probability_mono,
    ``RiffleLowerV2.Occupancy.probability_nonneg,
    ``RiffleLowerV2.Occupancy.probability_le_one,
    ``RiffleLowerV2.Occupancy.probability_true,
    ``RiffleLowerV2.Occupancy.probability_false,
    ``RiffleLowerV2.Occupancy.probability_not,
    ``RiffleLowerV2.Occupancy.probability_and_le_left,
    ``RiffleLowerV2.Occupancy.probability_and_le_right,
    ``RiffleLowerV2.Occupancy.expect_indicator_mul,
    ``RiffleLowerV2.Occupancy.variance_eq,
    ``RiffleLowerV2.Occupancy.variance_nonneg,
    ``RiffleLowerV2.Occupancy.chebyshev,
    ``RiffleLowerV2.Occupancy.chebyshev_of_variance_le,
    ``RiffleLowerV2.Occupancy.lower_tail_success,
    ``RiffleLowerV2.Occupancy.positive_success,
    ``RiffleLowerV2.Occupancy.eventCount,
    ``RiffleLowerV2.Occupancy.eventCount_nonneg,
    ``RiffleLowerV2.Occupancy.expect_eventCount,
    ``RiffleLowerV2.Occupancy.expect_eventCount_sq,
    ``RiffleLowerV2.Occupancy.variance_eventCount,
    ``RiffleLowerV2.Occupancy.variance_eventCount_le,
    ``RiffleLowerV2.Occupancy.variance_collisionCount_le]
  for name in names do
    let some info := env.find? name | throwError "Missing export {name}"
    let dependencies ← Lean.collectAxioms name
    for ax in dependencies do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected trusted closure at {name}: {ax}"
    let typ ← liftTermElabM <| Meta.ppExpr info.type
    let data := Json.mkObj [("name", toJson name.toString),
      ("kind", toJson (if info.isTheorem then "theorem" else "definition")),
      ("type", toJson typ.pretty), ("axioms", toJson (dependencies.map Name.toString))]
    logInfo m!"LB08_PROBABILITY_DECLARATION_JSON {data.compress}"
