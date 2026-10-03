import RiffleUpperV2.Anchor.Main

set_option maxHeartbeats 0
set_option pp.all true
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for name in [``RiffleUpperV2.Anchor.endpointSmoothing,
      ``RiffleUpperV2.Anchor.endpointShiftHypergeometric,
      ``RiffleUpperV2.Anchor.smoothingFailure,
      ``RiffleUpperV2.Anchor.endpointVariance,
      ``RiffleUpperV2.Anchor.conditionalEndpointAtoms,
      ``RiffleUpperV2.Anchor.jointInternalOffsetAtoms] do
    let some ci := env.find? name | throwError "Missing public theorem {name}"
    let ty ← liftTermElabM <| Meta.ppExpr ci.type
    let row := Json.mkObj [("name", toJson name.toString), ("fully_explicit_type", toJson ty.pretty)]
    logInfo m!"U03_PUBLIC_TYPE_JSON {row.compress}"
