"""Generate an independent environment audit without modifying package sources."""
from pathlib import Path
import json, sys

A = Path(__file__).resolve().parent
R = A.parents[1]
version = sys.argv[1]
all_modules = '--all' in sys.argv[2:]
modules = ['RiffleLowerV2.MacroscopicLower.Main']
if all_modules:
    modules = sorted({'.'.join(p.relative_to(R).with_suffix('').parts)
        for folder in ['RiffleLowerV2', 'Contracts'] for p in (R/folder).rglob('*.lean')}
        | {'RiffleLowerV2', 'Contracts'})
required = [(e['name'], e['type']) for row in json.loads((R/'OWNERSHIP.json').read_text()).values()
            for e in row.get('required_exports', [])]
if not all_modules:
    required = [(n,t) for n,t in required if '.EmpiricalLower.' in n or '.MacroscopicLower.' in n]
header = '\n'.join('import '+m for m in modules)
names = '#[' + ',\n'.join('(`'+n+', `'+t+')' for n,t in required) + ']'
body = r'''
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
set_option pp.funBinderTypes true
set_option pp.universes false

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let required := REQUIRED
  for (name, target) in required do
    let some ci := env.find? name | throwError "Missing frozen export {name}"
    unless ci.isTheorem && ci.type.isConstOf target do
      throwError "Frozen export is not a theorem of its exact target: {name}"
    logInfo m!"EXACT_EXPORT_JSON {(Json.mkObj [("name", toJson name.toString), ("target", toJson target.toString)]).compress}"
  for (name, ci) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.allImportedModuleNames[idx]!.toString
      | none => ""
    if moduleName.startsWith "RiffleLowerV2" || moduleName.startsWith "Contracts" ||
        moduleName.startsWith "RiffleTimeProfile" || moduleName.startsWith "RiffleShuffle" then
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Illicit axiom dependency {ax} of {name}"
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .opaqueInfo _ => "opaque"
        | _ => "generated"
      if kind == "axiom" then throwError "Project axiom {name}"
      let ty ← liftTermElabM <| Meta.ppExpr ci.type
      let deps := (ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
      let val ← match ci.value? (allowOpaque := true) with
        | some v => do
            if ci.type.isSort then
              let doc ← liftTermElabM <| Meta.ppExpr v
              pure doc.pretty
            else pure ""
        | none => pure ""
      let row := Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName),
        ("kind", toJson kind), ("type", toJson ty.pretty), ("value", toJson val),
        ("type_dependencies", toJson (ci.type.getUsedConstants.map Name.toString)),
        ("value_dependencies", toJson (deps.map Name.toString)),
        ("all_direct_dependencies", toJson (ci.getUsedConstantsAsSet.toArray.map Name.toString)),
        ("axioms", toJson (axs.map Name.toString))]
      logInfo m!"DECLARATION_JSON {row.compress}"
  for root in #[`RiffleLowerV2.EmpiricalLower.empiricalCombined,
      `RiffleLowerV2.EmpiricalLower.coldOnly,
      `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable,
      `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto] do
    let mut queue := #[root]
    let mut seen : NameSet := {}
    let mut allNames : Array String := #[]
    let mut axioms : Array String := #[]
    let mut project : Array String := #[]
    while !queue.isEmpty do
      let name := queue.back!
      queue := queue.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some ci := env.find? name | throwError "Absent transitive dependency {name}"
      queue := queue ++ ci.getUsedConstantsAsSet.toArray
      allNames := allNames.push name.toString
      match ci with
      | .axiomInfo _ =>
        unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
          throwError "Forbidden axiom {name} in endpoint closure {root}"
        axioms := axioms.push name.toString
      | _ => pure ()
      let modName := match env.getModuleIdxFor? name with
        | some idx => env.allImportedModuleNames[idx]!.toString
        | none => ""
      if modName.startsWith "RiffleLowerV2" || modName.startsWith "Contracts" ||
          modName.startsWith "RiffleTimeProfile" || modName.startsWith "RiffleShuffle" then
        project := project.push name.toString
    let axs ← Lean.collectAxioms root
    logInfo m!"CLOSURE_JSON {(Json.mkObj [("root", toJson root.toString), ("reachable_count", toJson allNames.size), ("all_reachable_names", toJson allNames), ("project_reachable_names", toJson project), ("recursive_axioms", toJson axioms), ("collect_axioms", toJson (axs.map Name.toString))]).compress}"
  logInfo m!"MODULES_JSON {toJson (env.allImportedModuleNames.map Name.toString)}"


example {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) :
    RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts) (RiffleLowerV2.uniformPermutation N) =
    RiffleLowerV2.tv (RiffleLowerV2.physicalForwardLaw cuts) (RiffleLowerV2.uniformPermutation N) := by
  rw [RiffleLowerV2.physicalInverseLaw_eq_map]
  exact RiffleLowerV2.Model.inversionTV N _

#print RiffleLowerV2.EmpiricalLower.empiricalCombined
#print RiffleLowerV2.MacroscopicLower.macroscopicIntegrable
#print RiffleLowerV2.Targets.EmpiricalCombinedTarget
#print RiffleLowerV2.Targets.MacroscopicIntegrableTarget
#print RiffleLowerV2.ScalarIntegrable
#print RiffleLowerV2.ColdWitnessData
#print RiffleLowerV2.RoundedTypeData
#print RiffleLowerV2.ColdGeometryData
#print RiffleLowerV2.WitnessSpec
#print RiffleLowerV2.GeometrySpec
#print RiffleLowerV2.TypeDataSpec

open Lean Elab Command in
run_cmd logInfo "LB12_INDEPENDENT_AUDIT_PASSED"
'''
with (A/f'IndependentCheck_{version}.lean').open('x') as f:
    f.write(header + '\n' + body.replace('REQUIRED', names))
with (A/f'check_inputs_{version}.json').open('x') as f:
    json.dump({'modules': modules, 'required_exports': dict(required)}, f, indent=2)
print(f'Generated IndependentCheck_{version}.lean: {len(modules)} imports; {len(required)} exact exports')
