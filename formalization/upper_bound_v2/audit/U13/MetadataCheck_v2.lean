import RiffleUpperV2.Completed
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
set_option pp.funBinderTypes true
set_option pp.universes false

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let names := #[
    ``RiffleUpperV2.FirstMoment.empiricalFirstMoment,
    ``RiffleUpperV2.Conditional.remainingCommonEdges,
    ``RiffleUpperV2.EmpiricalUpper.empiricalUpper,
    ``RiffleUpperV2.ProfileUpper.bufferedUpper,
    ``RiffleUpperV2.ProfileUpper.criticalTimeUpper,
    ``RiffleUpperV2.ProfileUpper.randomUpper,
    ``RiffleUpperV2.ProfileUpper.randomEmpiricalBound,
    ``RiffleUpperV2.ProfileUpper.randomEmpiricalUpper,
    ``RiffleUpperV2.ProfileUpper.randomProfileUpper,
    ``RiffleUpperV2.ArbitrarilyFineApproximation,
    ``RiffleUpperV2.EmpiricalNegativeMargin,
    ``RiffleUpperV2.Exploration.pairHistoryGood,
    ``RiffleUpperV2.Exploration.remainingDirectionalCount,
    ``RiffleUpperV2.criticalTime_empty,
    ``RiffleUpperV2.mixingTime_empty]
  let mut rows : Array Json := #[]
  for name in names do
    let ci ← getConstInfo name
    let ty ← liftTermElabM <| Meta.withTransparency .all do
      Meta.ppExpr (← Meta.whnf ci.type)
    let value ← match ci.value? (allowOpaque := true) with
      | some v => do
        let pp ← liftTermElabM <| Meta.ppExpr v
        pure pp.pretty
      | none => pure ""
    let axs ← Lean.collectAxioms name
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("expanded_type", toJson ty.pretty),
      ("value", toJson value), ("axioms", toJson (axs.map Name.toString))]
  let obj := Json.mkObj [
    ("imported_modules", toJson (env.allImportedModuleNames.map Name.toString)),
    ("expanded_declarations", toJson rows)]
  liftIO <| IO.FS.writeFile "audit/U13/final-metadata-v2.json" (obj.pretty 120)
  logInfo m!"U13_METADATA_PASS modules={env.allImportedModuleNames.size} declarations={rows.size}"

example : RiffleUpperV2.Contracts.V1.REmpiricalBound :=
  RiffleUpperV2.ProfileUpper.randomEmpiricalBound
example : RiffleUpperV2.Contracts.V1.REmpirical :=
  RiffleUpperV2.ProfileUpper.randomEmpiricalUpper
example : RiffleUpperV2.Contracts.V1.RProfile :=
  RiffleUpperV2.ProfileUpper.randomProfileUpper
