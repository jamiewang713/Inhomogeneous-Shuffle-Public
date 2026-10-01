import RiffleLowerV2.Occupancy.Conditional
import Lean.Util.CollectAxioms

set_option pp.universes false
set_option pp.funBinderTypes true

example : RiffleLowerV2.Targets.ConditionalCollisionStability :=
  RiffleLowerV2.Occupancy.conditionalCollisionStability

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RiffleLowerV2.Occupancy.logScale_le_two_logScale_sub,
    ``RiffleLowerV2.Occupancy.tau_sub_le_two_tau,
    ``RiffleLowerV2.Occupancy.eventual_residual_budgets,
    ``RiffleLowerV2.Occupancy.residual_selected_piles,
    ``RiffleLowerV2.Occupancy.conditionalCollisionStability]
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
    logInfo m!"LB08_CONDITIONAL_DECLARATION_JSON {data.compress}"
