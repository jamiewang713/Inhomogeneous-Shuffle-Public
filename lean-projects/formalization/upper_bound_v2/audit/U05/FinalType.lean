import RiffleUpperV2.FirstMoment.Empirical
import Lean
set_option pp.fullNames true
set_option pp.universes true
set_option maxHeartbeats 0
#print RiffleUpperV2.Contracts.V1.F
#print axioms RiffleUpperV2.FirstMoment.empiricalFirstMoment
open Lean Elab Command in
run_cmd do
  let ci ← getConstInfo ``RiffleUpperV2.FirstMoment.empiricalFirstMoment
  let ty ← liftTermElabM <| Meta.whnf ci.type
  let pp ← liftTermElabM <| Meta.ppExpr ty
  logInfo m!"U05_F_EXPANDED_TYPE {pp}"
#check @RiffleUpperV2.FirstMoment.empiricalGraphDecay
#print axioms RiffleUpperV2.FirstMoment.empiricalGraphDecay
