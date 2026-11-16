import RiffleUpperV2.Conditional.Main
import Lean
set_option pp.fullNames true
set_option pp.universes true
set_option maxHeartbeats 0
#check (show RiffleUpperV2.Contracts.V1.C from RiffleUpperV2.Conditional.remainingCommonEdges)
#print RiffleUpperV2.Contracts.V1.C
#print axioms RiffleUpperV2.Conditional.remainingCommonEdges
open Lean Elab Command in
run_cmd do
  let ci ← getConstInfo ``RiffleUpperV2.Conditional.remainingCommonEdges
  let ty ← liftTermElabM <| Meta.whnf ci.type
  let pp ← liftTermElabM <| Meta.ppExpr ty
  logInfo m!"U09_C_EXPANDED_TYPE {pp}"
#check @RiffleUpperV2.Conditional.oneHistory_uniform
#print axioms RiffleUpperV2.Conditional.oneHistory_uniform
