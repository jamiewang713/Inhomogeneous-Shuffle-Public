import RiffleUpperV2.ProfileUpper.Main
import RiffleUpperV2.Conditional.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

namespace RiffleUpperV2.Completed
 theorem firstMoment : Contracts.V1.F := FirstMoment.empiricalFirstMoment
 theorem conditionalEdges : Contracts.V1.C := Conditional.remainingCommonEdges
 theorem empiricalUpper : Contracts.V1.E := EmpiricalUpper.empiricalUpper
 theorem profileUpper : Contracts.V1.P := ProfileUpper.bufferedUpper
 theorem criticalUpper : Contracts.V1.T := ProfileUpper.criticalTimeUpper
 theorem randomUpper : Contracts.V1.R := ProfileUpper.randomUpper
end RiffleUpperV2.Completed
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option pp.funBinderTypes true
set_option pp.proofs false
set_option pp.universes false

open Lean Elab Command

private def auditDeps (ci : ConstantInfo) : NameSet := Id.run do
  let mut deps := ci.getUsedConstantsAsSet
  match ci with
  | .inductInfo v =>
    for n in v.all do deps := deps.insert n
    for n in v.ctors do deps := deps.insert n
  | .ctorInfo v => deps := deps.insert v.induct
  | .recInfo v =>
    for n in v.all do deps := deps.insert n
    for r in v.rules do
      deps := deps.insert r.ctor
      deps := deps ++ r.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return deps

private def auditKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

run_cmd do
  let env := (← getEnv).setExporting false
  let targets := #[
    ``RiffleUpperV2.FirstMoment.empiricalFirstMoment,
    ``RiffleUpperV2.Conditional.remainingCommonEdges,
    ``RiffleUpperV2.EmpiricalUpper.empiricalUpper,
    ``RiffleUpperV2.ProfileUpper.bufferedUpper,
    ``RiffleUpperV2.ProfileUpper.criticalTimeUpper,
    ``RiffleUpperV2.ProfileUpper.randomUpper,
    ``RiffleUpperV2.Completed.firstMoment,
    ``RiffleUpperV2.Completed.conditionalEdges,
    ``RiffleUpperV2.Completed.empiricalUpper,
    ``RiffleUpperV2.Completed.profileUpper,
    ``RiffleUpperV2.Completed.criticalUpper,
    ``RiffleUpperV2.Completed.randomUpper]
  let mut roots : Array Json := #[]
  let mut allVisited : NameSet := {}
  for root in targets do
    let some rootInfo := env.checked.get.find? root | throwError "Missing root {root}"
    unless rootInfo matches .thmInfo _ do throwError "Root is not a theorem: {root}"
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut foundAxioms : NameSet := {}
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      unless seen.contains name do
        seen := seen.insert name
        allVisited := allVisited.insert name
        let some ci := env.checked.get.find? name | throwError "Missing dependency {name}"
        if ci matches .axiomInfo _ then
          foundAxioms := foundAxioms.insert name
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains name do
            throwError "Nonstandard axiom {name} in {root}"
        for dep in auditDeps ci do
          unless seen.contains dep do todo := todo.push dep
    let collected ← Lean.collectAxioms root
    let manual := foundAxioms.toArray.qsort Name.lt
    unless manual == collected.qsort Name.lt do
      throwError "Axiom traversal mismatch in {root}: manual {manual}; collector {collected}"
    let ty ← liftTermElabM <| Meta.withTransparency .all do
      Meta.ppExpr (← Meta.whnf rootInfo.type)
    roots := roots.push <| Json.mkObj [
      ("name", toJson root.toString), ("expanded_type", toJson ty.pretty),
      ("recursive_dependency_count", toJson seen.size),
      ("axioms", toJson (manual.map Name.toString)),
      ("collector_matches_manual_traversal", toJson true),
      ("dependencies", toJson (seen.toArray.map Name.toString))]
  let mut rows : Array Json := #[]
  for name in allVisited do
    let some ci := env.checked.get.find? name | throwError "Missing inventory dependency"
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.allImportedModuleNames[idx]!.toString
      | none => ""
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName),
      ("kind", toJson (auditKind ci)),
      ("body_available", toJson (ci.value? (allowOpaque := true)).isSome),
      ("direct_dependencies", toJson ((auditDeps ci).toArray.map Name.toString))]
  let mut projectRows : Array Json := #[]
  for (name, ci) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.allImportedModuleNames[idx]!.toString
      | none => ""
    if moduleName.startsWith "RiffleUpperV2" then
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Nonstandard project axiom {ax} in {name}"
      unless auditKind ci != "axiom" do throwError "Project axiom {name}"
      projectRows := projectRows.push <| Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName),
        ("kind", toJson (auditKind ci)),
        ("axioms", toJson (axs.map Name.toString))]
  let result := Json.mkObj [("status", toJson "TRUST_PASS"),
    ("roots", toJson roots), ("recursive_inventory", toJson rows),
    ("all_upper_declarations", toJson projectRows)]
  liftIO <| IO.FS.writeFile "audit/U13/development-trust-v2.json" (result.pretty 120)
  logInfo m!"U13_INDEPENDENT_TRUST_PASS roots={roots.size} dependencies={rows.size} upper_declarations={projectRows.size}"

example : RiffleUpperV2.Contracts.V1.F := RiffleUpperV2.Completed.firstMoment
example : RiffleUpperV2.Contracts.V1.C := RiffleUpperV2.Completed.conditionalEdges
example : RiffleUpperV2.Contracts.V1.E := RiffleUpperV2.Completed.empiricalUpper
example : RiffleUpperV2.Contracts.V1.P := RiffleUpperV2.Completed.profileUpper
example : RiffleUpperV2.Contracts.V1.T := RiffleUpperV2.Completed.criticalUpper
example : RiffleUpperV2.Contracts.V1.R := RiffleUpperV2.Completed.randomUpper
