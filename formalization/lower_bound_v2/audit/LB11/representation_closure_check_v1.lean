import RiffleLowerV2.MacroscopicLower.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
set_option pp.funBinderTypes true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let endpoint := `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable
  let wrapper := `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto
  let some info := env.find? endpoint | throwError "Missing endpoint"
  unless info.isTheorem && info.type.isConstOf `RiffleLowerV2.Targets.MacroscopicIntegrableTarget do
    throwError "Required endpoint is not a theorem of the exact frozen target"
  for root in #[endpoint, wrapper] do
    let mut queue := #[root]
    let mut seen : NameSet := {}
    let mut axioms : Array String := #[]
    let mut allNames : Array String := #[]
    let mut project : Array Json := #[]
    while !queue.isEmpty do
      let name := queue.back!
      queue := queue.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some ci := env.find? name | throwError "Missing dependency {name}"
      let typeDeps := ci.type.getUsedConstants
      let valueDeps := match ci.value? (allowOpaque := true) with
        | some value => value.getUsedConstants
        | none => #[]
      queue := queue ++ typeDeps ++ valueDeps
      allNames := allNames.push name.toString
      match ci with
      | .axiomInfo _ =>
        unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
          throwError "Unexpected axiom in complete recursive closure: {name}"
        axioms := axioms.push name.toString
      | _ => pure ()
      if name.toString.startsWith "RiffleLowerV2." ||
          name.toString.startsWith "TimeProfile." ||
          name.toString.startsWith "_private.RiffleLowerV2." then
        project := project.push <| Json.mkObj [
          ("name", toJson name.toString),
          ("type_dependencies", toJson (typeDeps.map Name.toString)),
          ("value_dependencies", toJson (valueDeps.map Name.toString))]
    let independentlyCollected ← Lean.collectAxioms root
    let record := Json.mkObj [
      ("root", toJson root.toString),
      ("reachable_count", toJson allNames.size),
      ("recursive_axioms", toJson axioms),
      ("collect_axioms", toJson (independentlyCollected.map Name.toString)),
      ("all_reachable_names", toJson allNames),
      ("project_dependency_graph", toJson project)]
    logInfo m!"REPRESENTATION_CLOSURE_JSON {record.compress}"
  logInfo "LB11_INDEPENDENT_REPRESENTATION_CLOSURE_PASSED"

#print RiffleLowerV2.Targets.MacroscopicIntegrableTarget
#print RiffleLowerV2.ScalarIntegrable
#check RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto
#print axioms RiffleLowerV2.MacroscopicLower.macroscopicIntegrable
#print axioms RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto
