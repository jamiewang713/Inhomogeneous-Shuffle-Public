#!/usr/bin/env python3
"""Complete metadata-aware audit of an existing fresh full_check_v1 build; no rebuild."""
from pathlib import Path
import argparse,datetime,fcntl,hashlib,importlib.util,json,os,subprocess,sys
import full_check_v1 as base
ROOT=base.ROOT
sha,read,create,require=base.sha,base.read,base.create,base.require

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--build-run',default='v1');ap.add_argument('--run',default='v3');a=ap.parse_args()
 require(base.re.fullmatch(r'v[1-9][0-9]*',a.build_run) and base.re.fullmatch(r'v[1-9][0-9]*',a.run),'Expected version labels')
 os.chdir(ROOT)
 lock=(ROOT/'.build/full-check.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 built=ROOT/'audit/LB00'/('full_package_'+a.build_run);out=ROOT/'audit/LB00'/('final_audit_'+a.run);lib=ROOT/'.build'/('full_package_'+a.build_run)/'lib/lean'
 require(not out.exists(),'Audit label already exists');require((built/'build.log').read_text().rstrip().endswith('BUILD_OK'),'Fresh source build not complete')
 provenance=read(built/'build_provenance.json');snapshot=read(built/'source_snapshot.json')
 modules=[str(Path(p).with_suffix('')).replace(os.sep,'.') for p in snapshot]
 require(set(modules)<=set(provenance['built']),'Package module not freshly rebuilt')
 for n,e in provenance['modules'].items():
  require(sha(e['source'])==e['sha256'],'Build source changed: '+n)
  if e['kind']=='project-rebuilt':require(n in provenance['built'],'Reached project module not rebuilt: '+n)
 for p,h in snapshot.items():require(sha(ROOT/p)==h,'Package source changed: '+p)
 spec=importlib.util.spec_from_file_location('frozen_builder',ROOT/'build.py');b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
 require(sha(b.COMPILER)==base.COMPILER_SHA,'Compiler changed')
 require(sha(ROOT/'Contracts/v1/SHA256.json')==base.BASE_SHA,'Foundation manifest changed')
 ledger=read(ROOT/'audit/LB00/INTEGRATION_LEDGER_v10.json');exports=ledger['required_exports'];out.mkdir()
 source=base.audit_source(modules,exports)
 source=source.replace('let env ← getEnv', 'let env := (← getEnv).setExporting false')
 source=source.replace('let prefix :=', 'let moduleRoot :=').replace('prefix ==', 'moduleRoot ==')
 # v1 generator replaced a placeholder inside the diagnostic marker. Preserve it and
 # write this corrected source separately, with all metadata edges included.
 source=source.replace('IMPORTED_'+', '.join(json.dumps(n) for n in modules)+'_JSON','IMPORTED_MODULES_JSON')
 old='''      let typeDeps := ci.type.getUsedConstants
      let valueDeps := match ci.value? (allowOpaque := true) with
        | some value => value.getUsedConstants
        | none => #[]
      queue := queue ++ typeDeps ++ valueDeps'''
 require(old in source,'Unexpected v1 recursive checker template')
 source=source.replace(old,'      queue := queue ++ ci.getUsedConstantsAsSet.toArray')
 source=source.replace('("type_dependencies", toJson typeDeps), ("value_dependencies", toJson valueDeps),','("type_dependencies", toJson typeDeps), ("value_dependencies", toJson valueDeps),\n        ("dependencies", toJson (info.getUsedConstantsAsSet.toArray.map Name.toString)),')
 create(out/'FullCheck.lean',source)
 owners=read(ROOT/'OWNERSHIP.json');entries=[owners[f'LB{i:02}']['proof_entry_point'] for i in range(1,12)]
 lines=['import RiffleLowerV2.Completed','import Lean.Util.CollectAxioms','','set_option pp.universes false','set_option pp.funBinderTypes true','']
 for e in exports:lines.append(f"example : {e['type']} := {e['name']}")
 lines += ['','open Lean Elab Command in','run_cmd do','  let env ← getEnv','  for moduleName in #['+', '.join('`'+n for n in entries)+'] do','    unless env.header.moduleNames.contains moduleName do','      throwError "Completed umbrella missed lane entry point {moduleName}"','  for (name, target) in #['+', '.join('(`'+e['name']+', `'+e['type']+')' for e in exports)+'] do','    let some ci := env.find? name | throwError "Missing umbrella export {name}"','    unless ci.isTheorem && ci.type.isConstOf target do','      throwError "Wrong umbrella export type {name}"','    for ax in (← Lean.collectAxioms name) do','      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do','        throwError "Unexpected umbrella axiom {ax}"','  logInfo "COMPLETED_UMBRELLA_ONLY_58_THEOREMS_VERIFIED"','']
 create(out/'CompletedOnly.lean','\n'.join(lines))
 env=dict(os.environ,LEAN_PATH=str(lib));commands={}
 for filename,logname in [('FullCheck.lean','audit.log'),('CompletedOnly.lean','completed_only.log')]:
  command=[str(b.COMPILER),'-R',str(ROOT),'-DwarningAsError=true',str(out/filename)];commands[filename]=command
  with (out/logname).open('x') as log:subprocess.run(command,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
 create(out/'COMMANDS.json',{'commands':commands,'LEAN_PATH':str(lib),'invocation':[sys.executable,'scripts/final_audit_v3.py','--build-run',a.build_run,'--run',a.run]})
 raw=(out/'audit.log').read_text();only=(out/'completed_only.log').read_text()
 require('FULL_PACKAGE_58_REQUIRED_THEOREMS_AND_CLOSURES_VERIFIED' in raw,'Missing full audit marker')
 require('COMPLETED_UMBRELLA_ONLY_58_THEOREMS_VERIFIED' in only,'Missing umbrella-only marker')
 require(not any(x in raw+only for x in ['warning:','error:']),'Audit diagnostics')
 records={};closures={};imported=[]
 for line in raw.splitlines():
  if 'FULL_DECLARATION_JSON ' in line:
   x=json.loads(line.split('FULL_DECLARATION_JSON ',1)[1]);require(x['name'] not in records,'Duplicate declaration');records[x['name']]=x
  elif 'ENDPOINT_CLOSURE_JSON ' in line:
   x=json.loads(line.split('ENDPOINT_CLOSURE_JSON ',1)[1]);closures[x['root']]=x
  elif 'IMPORTED_MODULES_JSON ' in line:imported=json.loads(line.split('IMPORTED_MODULES_JSON ',1)[1])
 require(set(modules)<=set(imported),'Missing package module')
 for n,x in records.items():require(x['kind']!='axiom' and set(x['axioms'])<=base.ALLOWED,'Unexpected axiom '+n)
 for e in exports:require(records[e['name']]['kind']=='theorem' and records[e['name']]['type']==e['type'],'Wrong exact theorem '+e['name'])
 require(len(closures)==3,'Missing endpoint')
 for n,x in closures.items():require(set(x['recursive_axioms'])==set(x['collect_axioms'])==base.ALLOWED,'Closure disagreement '+n)
 comparisons={};differences=[]
 inventories={'foundation':ROOT/'audit/LB00/compiled-declarations.json'}
 inventories.update({lane:ROOT/f'audit/LB00/{lane}_integration_declarations_v1.json' for lane in ledger['completed_lanes']})
 for lane,p in inventories.items():
  old=read(p)
  if isinstance(old,list):old={x['name']:x for x in old}
  for n,x in old.items():
   require(n in records,'Integrated declaration absent '+n);y=records[n]
   for k in ['type','type_dependencies','value_dependencies','axioms']:
    if k not in x:continue
    equal=(set(x[k])==set(y[k])) if k.endswith('dependencies') or k=='axioms' else x[k]==y[k]
    if not equal:differences.append({'lane':lane,'name':n,'field':k,'previous':x[k],'fresh':y[k]})
   if x['kind']=='theorem':require(y['kind']=='theorem','Theorem kind changed '+n)
  comparisons[lane]=len(old)
 create(out/'inventory_differences.json',differences)
 require(not differences,'Compiled inventory differences require examination')
 by_module={}
 for n,x in records.items():by_module.setdefault(x['module'],[]).append(n)
 objects={};sources={};trees={}
 for n in imported:
  rel=Path(*n.split('.'));p=lib/rel.with_suffix('.olean')
  if not p.exists():p=b.COMPILER.parent.parent/'lib/lean'/rel.with_suffix('.olean')
  require(p.exists(),'Missing imported object '+n)
  objects[n]={}
  for suffix in ['.olean','.olean.private','.olean.server']:
   q=p.with_suffix(suffix)
   if q.exists():objects[n][suffix]={'resolved_path':str(q.resolve()),'sha256':sha(q)}
  project=b.PROJECTS.get(n.split('.')[0]);source=project/rel.with_suffix('.lean') if project else None
  if not project:
   for pkg in b.PACKAGES.iterdir():
    candidate=pkg/rel.with_suffix('.lean')
    if not candidate.exists():continue
    source=candidate
    if pkg.name not in trees:
     entries={}
     for row in subprocess.check_output(['git','-C',str(pkg),'ls-tree','-r','-z','HEAD']).split(b'\0'):
      if row:
       meta,path=row.split(b'\t',1);entries[path.decode()]=meta.split()[2].decode()
     trees[pkg.name]=entries
    data=source.read_bytes();digest=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    require(trees[pkg.name].get(str(source.relative_to(pkg)))==digest,'Pinned source differs from commit: '+str(source));break
  if source and source.exists():sources[n]={'source':str(source),'sha256':sha(source),'kind':'project' if project else 'pinned-library'}
 for p,h in snapshot.items():require(sha(ROOT/p)==h,'Package source changed during audit '+p)
 for n,e in provenance['modules'].items():require(sha(e['source'])==e['sha256'],'Build input changed '+n)
 create(out/'compiled_declarations.json',records);create(out/'endpoint_closures.json',closures);create(out/'declarations_by_module.json',by_module)
 create(out/'imported_objects.json',objects);create(out/'imported_sources.json',sources)
 summary={'status':'FRESH_BUILD_AND_METADATA_COMPLETE_AUDIT_PASSED','recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'fresh_build_evidence':str(built.relative_to(ROOT)),'isolated_output':str(lib.relative_to(ROOT)),'compiler':provenance['compiler'],'compiler_sha256':provenance['compiler_sha256'],'mathlib_commit':provenance['mathlib_commit'],'base_manifest_sha256':base.BASE_SHA,'package_modules':len(modules),'freshly_built_modules':len(provenance['built']),'declarations_audited':len(records),'required_theorems_exact_checked':58,'completed_only_theorems_exact_checked':58,'completed_only_lane_entry_points':11,'imported_modules':len(imported),'imported_sources_verified':len(sources),'exact_prior_inventory_matches':comparisons,'axiom_union':sorted({ax for x in records.values() for ax in x['axioms']}),'endpoint_closure_counts':{n:x['reachable_count'] for n,x in closures.items()},'recursive_dependencies':'ConstantInfo.getUsedConstantsAsSet: types, values (opaque opened), inductive constructors and recursor metadata','audit_warning_count':0,'build_warning_count':(built/'build.log').read_text().count('warning:'),'scope':'Empirical E; selected-partition scalar-integrable M; derived sequence corollary. No certification of the historical arbitrary-TimeLaw statement.'}
 create(out/'VERIFICATION.json',summary)
 bound={str(p.relative_to(ROOT)):sha(p) for p in out.iterdir() if p.is_file()}
 for p in built.iterdir():
  if p.is_file():bound[str(p.relative_to(ROOT))]=sha(p)
 for p in ['scripts/full_check_v1.py','scripts/final_audit_v3.py','RiffleLowerV2/Completed.lean','audit/LB00/COMPLETED_UMBRELLA_COMPARISON_v1.md','audit/LB00/INTEGRATION_LEDGER_v10.json']:bound[p]=sha(ROOT/p)
 create(out/'SHA256.json',bound)
 print(json.dumps(summary,indent=2),flush=True);print('FINAL_AUDIT_MANIFEST_SHA256',sha(out/'SHA256.json'),flush=True)
if __name__=='__main__':main()
