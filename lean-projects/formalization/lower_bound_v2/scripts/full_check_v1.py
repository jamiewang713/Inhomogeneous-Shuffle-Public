#!/usr/bin/env python3
"""Additive full-package verifier. Never edits the frozen foundation tools or evidence."""
from pathlib import Path
import argparse,datetime,fcntl,hashlib,importlib.util,json,os,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
WORK=ROOT.parent.parent
ALLOWED={'Classical.choice','Quot.sound','propext'}
BASE_SHA='4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858'
COMPILER_SHA='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def create(p,x):
 p=Path(p)
 with p.open('x') as f:
  if isinstance(x,str):f.write(x)
  else:json.dump(x,f,indent=2,sort_keys=True,ensure_ascii=False);f.write('\n')
def require(v,msg):
 if not v:raise RuntimeError(msg)
def audit_source(modules,exports):
 lines=['import '+n for n in modules]+['import Lean.Util.FoldConsts','import Lean.Util.CollectAxioms','','set_option pp.universes false','set_option pp.funBinderTypes true','set_option maxHeartbeats 0','']
 for e in exports:lines.append(f"example : {e['type']} := {e['name']}")
 pairs=',\n    '.join('(`'+e['name']+', `'+e['type']+')' for e in exports)
 lines.append('''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, target) in #[PAIRS] do
    let some ci := env.find? name | throwError "Missing required theorem {name}"
    unless ci.isTheorem && ci.type.isConstOf target do
      throwError "Wrong theorem kind or exact frozen type: {name}"
  let requiredModules : Array String := #[MODULES]
  for expected in requiredModules do
    unless env.header.moduleNames.any (fun n => n.toString == expected) do
      throwError "Required source module was not imported: {expected}"
  logInfo m!"IMPORTED_MODULES_JSON {(toJson (env.header.moduleNames.map Name.toString)).compress}"
  for (name, info) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => env.mainModule.toString
    let prefix := moduleName.splitOn "." |>.head!
    if prefix == "RiffleLowerV2" || prefix == "Contracts" ||
        prefix == "RiffleTimeProfile" || prefix == "RiffleShuffle" then
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected axiom closure at {name}: {ax}"
      let typeDeps := info.type.getUsedConstants.map Name.toString
      let valueDeps := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants.map Name.toString
        | none => #[]
      let typ ← liftTermElabM <| Meta.ppExpr info.type
      let val ← match info.value? (allowOpaque := true) with
        | some value => do
            if info.isTheorem then pure "" else
              let v ← liftTermElabM <| Meta.ppExpr value
              pure v.pretty
        | none => pure ""
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | _ => "generated"
      let row := Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName),
        ("kind", toJson kind), ("type", toJson typ.pretty), ("value", toJson val),
        ("type_dependencies", toJson typeDeps), ("value_dependencies", toJson valueDeps),
        ("axioms", toJson (axs.map Name.toString))]
      logInfo m!"FULL_DECLARATION_JSON {row.compress}"
  for root in #[`RiffleLowerV2.EmpiricalLower.empiricalCombined,
      `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable,
      `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto] do
    let mut queue := #[root]
    let mut seen : NameSet := {}
    let mut axioms : Array String := #[]
    let mut allNames : Array String := #[]
    while !queue.isEmpty do
      let name := queue.back!
      queue := queue.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some ci := env.find? name | throwError "Missing recursive dependency {name}"
      let typeDeps := ci.type.getUsedConstants
      let valueDeps := match ci.value? (allowOpaque := true) with
        | some value => value.getUsedConstants
        | none => #[]
      queue := queue ++ typeDeps ++ valueDeps
      allNames := allNames.push name.toString
      match ci with
      | .axiomInfo _ =>
        unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
          throwError "Unexpected recursively reached axiom {name}"
        axioms := axioms.push name.toString
      | _ => pure ()
    let collected ← Lean.collectAxioms root
    let row := Json.mkObj [("root", toJson root.toString),
      ("reachable_count", toJson allNames.size), ("all_reachable_names", toJson allNames),
      ("recursive_axioms", toJson axioms), ("collect_axioms", toJson (collected.map Name.toString))]
    logInfo m!"ENDPOINT_CLOSURE_JSON {row.compress}"
  logInfo "FULL_PACKAGE_58_REQUIRED_THEOREMS_AND_CLOSURES_VERIFIED"

#print RiffleLowerV2.Targets.EmpiricalCombinedTarget
#print RiffleLowerV2.Targets.MacroscopicIntegrableTarget
#print RiffleLowerV2.ScalarIntegrable
'''.replace('PAIRS',pairs).replace('MODULES',', '.join(json.dumps(n) for n in modules)))
 return '\n'.join(lines)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--run',required=True,help='New immutable run label, such as v1');args=ap.parse_args()
 require(re.fullmatch(r'v[1-9][0-9]*',args.run),'Expected v<number>')
 os.chdir(ROOT)
 lock=(ROOT/'.build/full-check.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 evidence=ROOT/'audit/LB00'/('full_package_'+args.run);output=ROOT/'.build'/('full_package_'+args.run);lib=output/'lib/lean'
 require(not evidence.exists() and not output.exists(),'Run already exists; choose a new label')
 evidence.mkdir();output.mkdir()
 spec=importlib.util.spec_from_file_location('frozen_builder',ROOT/'build.py');b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
 require(sha(ROOT/'Contracts/v1/SHA256.json')==BASE_SHA,'Frozen manifest changed')
 require(sha(b.COMPILER)==COMPILER_SHA,'Compiler fingerprint changed')
 ledger=read(ROOT/'audit/LB00/INTEGRATION_LEDGER_v10.json');exports=ledger['required_exports']
 require(len(exports)==58 and all(e['integration_status']=='PROVED_AND_INTEGRATED' for e in exports),'Incomplete integrated target ledger')
 paths=sorted([ROOT/'RiffleLowerV2.lean',ROOT/'Contracts.lean']+[p for folder in ['RiffleLowerV2','Contracts'] for p in (ROOT/folder).rglob('*.lean')])
 modules=[str(p.relative_to(ROOT).with_suffix('')).replace(os.sep,'.') for p in paths]
 snapshot={str(p.relative_to(ROOT)):sha(p) for p in paths};create(evidence/'source_snapshot.json',snapshot)
 create(evidence/'FullCheck.lean',audit_source(modules,exports))
 create(evidence/'REQUIRED_EXPORTS.json',exports)
 checks={}
 with (evidence/'preflight.log').open('x') as log:
  for receipt in sorted(p.name for p in (ROOT/'Contracts/dependencies').iterdir() if p.is_dir()):
   text=subprocess.check_output([sys.executable,'scripts/check_dependency_receipt.py',receipt,'--sources-only'],text=True);log.write(text);checks[receipt]=text.strip()
 print('FULL_PREFLIGHT_OK',len(checks),'receipts;',len(modules),'source modules',flush=True)
 code="import importlib.util,pathlib,sys; spec=importlib.util.spec_from_file_location('frozen_builder','build.py'); b=importlib.util.module_from_spec(spec); spec.loader.exec_module(b); b.LIB=pathlib.Path(sys.argv[1]); sys.argv=['build.py','--fresh']+sys.argv[2:]; b.main()"
 command=[sys.executable,'-c',code,str(lib),*modules]
 audit_command=[str(b.COMPILER),'-R',str(ROOT),'-DwarningAsError=true',str(evidence/'FullCheck.lean')]
 create(evidence/'COMMANDS.json',{'build':command,'audit':audit_command,'LEAN_PATH':str(lib),'invocation':[sys.executable,'scripts/full_check_v1.py','--run',args.run],'build_scope':'Every package source module and every reached canonical project module freshly rebuilt in an initially absent output tree. Only pinned third-party library caches are reused read-only. No shared or lane project outputs are copied.'})
 with (evidence/'build.log').open('x') as log:subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
 provenance=read(ROOT/'.build/provenance.json');create(evidence/'build_provenance.json',provenance)
 require(set(modules)<=set(provenance['built']),'Some package modules were not freshly rebuilt')
 for n,e in provenance['modules'].items():
  require(sha(e['source'])==e['sha256'],'Source changed during build: '+n)
  if e['kind']=='project-rebuilt':require(n in provenance['built'],'Project input not freshly rebuilt: '+n)
 for p,h in snapshot.items():require(sha(ROOT/p)==h,'Package source changed during build: '+p)
 print('FULL_FRESH_BUILD_OK',len(provenance['built']),'rebuilt modules',flush=True)
 env=dict(os.environ,LEAN_PATH=str(lib))
 with (evidence/'audit.log').open('x') as log:subprocess.run(audit_command,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
 raw=(evidence/'audit.log').read_text();require('FULL_PACKAGE_58_REQUIRED_THEOREMS_AND_CLOSURES_VERIFIED' in raw,'Missing completed audit marker')
 require('warning:' not in raw and 'error:' not in raw,'Audit diagnostics')
 records={};closures={};imported=[]
 for line in raw.splitlines():
  if 'FULL_DECLARATION_JSON ' in line:
   x=json.loads(line.split('FULL_DECLARATION_JSON ',1)[1]);require(x['name'] not in records,'Duplicate declaration');records[x['name']]=x
  elif 'ENDPOINT_CLOSURE_JSON ' in line:
   x=json.loads(line.split('ENDPOINT_CLOSURE_JSON ',1)[1]);closures[x['root']]=x
  elif 'IMPORTED_MODULES_JSON ' in line:imported=json.loads(line.split('IMPORTED_MODULES_JSON ',1)[1])
 for n,x in records.items():require(x['kind']!='axiom' and set(x['axioms'])<=ALLOWED,'Invalid declaration '+n)
 for e in exports:
  x=records[e['name']];require(x['kind']=='theorem' and x['type']==e['type'],'Wrong required type '+e['name'])
 require(len(closures)==3,'Missing endpoint closure')
 for n,x in closures.items():require(set(x['recursive_axioms'])==set(x['collect_axioms'])<=ALLOWED,'Closure mismatch '+n)
 require(set(modules)<=set(imported),'Audit omitted a package source module')
 # Attribute declarations to compiler-provided defining modules, never flat namespace guesses.
 by_module={}
 for n,x in records.items():by_module.setdefault(x['module'],[]).append(n)
 cache_inputs={};source_inputs={};package_trees={}
 for n in imported:
  rel=Path(*n.split('.'));p=lib/rel.with_suffix('.olean')
  if not p.exists():p=b.COMPILER.parent.parent/'lib/lean'/rel.with_suffix('.olean')
  require(p.exists(),'Missing actual imported object '+n)
  companions={}
  for suffix in ['.olean','.olean.private','.olean.server']:
   q=p.with_suffix(suffix)
   if q.exists():companions[suffix]={'resolved_path':str(q.resolve()),'sha256':sha(q)}
  cache_inputs[n]=companions
  source=None
  project=b.PROJECTS.get(n.split('.')[0])
  if project:source=project/rel.with_suffix('.lean')
  else:
   for pkg in b.PACKAGES.iterdir():
    candidate=pkg/rel.with_suffix('.lean')
    if not candidate.exists():continue
    source=candidate
    if pkg.name not in package_trees:
     tree=subprocess.check_output(['git','-C',str(pkg),'ls-tree','-r','-z','HEAD']);entries={}
     for entry in tree.split(b'\0'):
      if entry:
       meta,path=entry.split(b'\t',1);entries[path.decode()]=meta.split()[2].decode()
     package_trees[pkg.name]=entries
    data=source.read_bytes();git_hash=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    require(package_trees[pkg.name].get(str(source.relative_to(pkg)))==git_hash,'Pinned source differs from HEAD: '+str(source))
    break
  if source and source.exists():source_inputs[n]={'source':str(source),'sha256':sha(source),'kind':'project' if project else 'pinned-library'}
 for p,h in snapshot.items():require(sha(ROOT/p)==h,'Package source changed during audit: '+p)
 for n,e in provenance['modules'].items():require(sha(e['source'])==e['sha256'],'Dependency changed during audit: '+n)
 # Every previously integrated declaration must occur in this full environment.
 inventory_comparisons={}
 for lane in ledger['completed_lanes']:
  p=ROOT/f'audit/LB00/{lane}_integration_declarations_v1.json'
  if not p.exists():continue
  old=read(p)
  if isinstance(old,list):old={x['name']:x for x in old}
  for n,x in old.items():
   require(n in records,'Missing integrated declaration '+n)
   require(set(x['axioms'])==set(records[n]['axioms']),'Axiom inventory changed '+n)
   if x['kind']=='theorem':require(records[n]['kind']=='theorem','Theorem kind changed '+n)
  inventory_comparisons[lane]=len(old)
 create(evidence/'compiled_declarations.json',records);create(evidence/'endpoint_closures.json',closures)
 create(evidence/'declarations_by_module.json',by_module);create(evidence/'imported_objects.json',cache_inputs);create(evidence/'imported_sources.json',source_inputs)
 summary={'status':'FRESH_FULL_PACKAGE_BUILD_AND_AUDIT_PASSED','recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base_manifest_sha256':BASE_SHA,'compiler':provenance['compiler'],'compiler_sha256':provenance['compiler_sha256'],'mathlib_commit':provenance['mathlib_commit'],'dependency_revisions':read(ROOT/'Contracts/v1/SOURCES.json')['dependency_revisions'],'isolated_output':str(lib.relative_to(ROOT)),'package_modules':len(modules),'freshly_built_modules':len(provenance['built']),'declarations_audited':len(records),'required_theorems_exact_checked':58,'imported_modules':len(imported),'imported_source_files':len(source_inputs),'inventory_comparisons':inventory_comparisons,'axiom_union':sorted({a for x in records.values() for a in x['axioms']}),'endpoint_closure_counts':{n:x['reachable_count'] for n,x in closures.items()},'build_warning_count':(evidence/'build.log').read_text().count('warning:'),'audit_warning_count':0,'scope':'Empirical E and selected-partition scalar-integrable M plus sequence corollary. Historical arbitrary-TimeLaw endpoint is not certified.'}
 create(evidence/'VERIFICATION.json',summary)
 bound={str(p.relative_to(ROOT)):sha(p) for p in evidence.iterdir() if p.is_file()}
 bound['scripts/full_check_v1.py']=sha(Path(__file__));bound['RiffleLowerV2/Completed.lean']=sha(ROOT/'RiffleLowerV2/Completed.lean')
 bound['audit/LB00/COMPLETED_UMBRELLA_COMPARISON_v1.md']=sha(ROOT/'audit/LB00/COMPLETED_UMBRELLA_COMPARISON_v1.md')
 create(evidence/'SHA256.json',bound)
 print(json.dumps(summary,indent=2),flush=True)
 print('FULL_PACKAGE_MANIFEST_SHA256',sha(evidence/'SHA256.json'),flush=True)
if __name__=='__main__':main()
