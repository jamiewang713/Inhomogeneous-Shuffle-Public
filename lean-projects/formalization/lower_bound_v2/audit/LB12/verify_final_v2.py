"""Independent final LB12 verification, using an already completed clean coordinator build.

Usage: python3 audit/LB12/verify_final_v2.py v5 audit/LB00/full_package_v1
Only new files in audit/LB12 are written. Project/library outputs remain read-only.
"""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

A = Path(__file__).resolve().parent
R = A.parents[1]
W = R.parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
COMPILER = Path('/Users/jialushi/Documents/loop soup/formalization/.tools/lean-4.33.1-darwin_aarch64/bin/lean')

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def save(p, data):
    with p.open('x') as f:
        if isinstance(data, str): f.write(data)
        else: json.dump(data, f, indent=2, ensure_ascii=False); f.write('\n')
def require(condition, msg):
    if not condition: raise RuntimeError(msg)

def check_hashes(base, rows):
    for rel, expected in rows.items():
        require(sha(base/rel) == expected, 'Fingerprint changed: '+str(base/rel))

def run_lean(source, log, lib):
    command = [str(COMPILER), '-DwarningAsError=true', '-R', str(R), str(source)]
    env = dict(os.environ, LEAN_PATH=str(lib))
    with log.open('x') as f:
        f.write('COMMAND '+repr(command)+'\nLEAN_PATH '+str(lib)+'\n'); f.flush()
        p = subprocess.run(command, cwd=R, env=env, stdout=f, stderr=subprocess.STDOUT)
        f.write('\nPROCESS_EXIT '+str(p.returncode)+'\n')
    require(p.returncode == 0, 'Lean check failed; see '+str(log))
    return log.read_text()

def main():
    version, evidence_rel = sys.argv[1:]
    require(re.fullmatch(r'v[1-9][0-9]*',version), 'Expected fresh version')
    evidence = R/evidence_rel
    verification = read(evidence/'VERIFICATION.json')
    require(verification['status'] == 'FRESH_FULL_PACKAGE_BUILD_AND_AUDIT_PASSED', 'Build not certified')
    check_hashes(R, read(evidence/'SHA256.json'))
    lib = R/verification['isolated_output']
    require(sha(COMPILER) == verification['compiler_sha256'], 'Compiler mismatch')
    before = read(A/'input_snapshot_v1.json')
    check_hashes(R, before['frozen_files'])
    check_hashes(W, before['external_files'])
    check_hashes(W, before['protected_old_files'])
    check_hashes(R, {x['path']:x['sha256'] for x in before['modules'].values()})
    snapshot = read(evidence/'source_snapshot.json')
    check_hashes(R, snapshot)
    modules = {'.'.join(Path(p).with_suffix('').parts) for p in snapshot}
    current = {'.'.join(p.relative_to(R).with_suffix('').parts)
        for folder in ['RiffleLowerV2','Contracts'] for p in (R/folder).rglob('*.lean')}
    current |= {'RiffleLowerV2', 'Contracts'}
    require(current == modules, 'Build missed current source modules')
    provenance = read(evidence/'build_provenance.json')
    require(modules <= set(provenance['built']), 'A module was not freshly compiled')
    require((evidence/'build.log').read_text().rstrip().endswith('BUILD_OK'), 'Build lacks terminal success')
    for n, entry in provenance['modules'].items():
        require(sha(Path(entry['source'])) == entry['sha256'], 'Imported source mismatch '+n)
        if entry['kind'] == 'project-rebuilt':
            require(n in provenance['built'], 'Canonical project source was not rebuilt '+n)
    # Every object actually used by the coordinator audit remains identical.
    objects = read(evidence/'imported_objects.json')
    def verify_objects():
        count = 0
        for module, companions in objects.items():
            rel = Path(*module.split('.'))
            base = lib/rel.with_suffix('.olean')
            if not base.exists():
                base = COMPILER.parent.parent/'lib/lean'/rel.with_suffix('.olean')
            for suffix, item in companions.items():
                actual = base.with_suffix(suffix)
                require(actual.is_file(), 'Missing imported object '+str(actual))
                require(str(actual.resolve()) == item['resolved_path'], 'Imported resolution changed '+module)
                require(sha(actual) == item['sha256'], 'Imported object changed '+module)
                count += 1
        return count
    object_count = verify_objects()
    # Independently verify every additive receipt's source/provenance closure.
    with (A/f'receipt_checks_{version}.log').open('x') as out:
        for p in sorted((R/'Contracts/dependencies').iterdir()):
            if p.is_dir():
                result = subprocess.run(['python3','scripts/check_dependency_receipt.py',p.name,'--sources-only'],
                    cwd=R,stdout=out,stderr=subprocess.STDOUT)
                require(result.returncode == 0,'Dependency receipt failed '+p.name)
    generated = subprocess.run(['python3',str(A/'generate_check_v5.py'),version,'--all'],cwd=R)
    require(generated.returncode == 0,'Audit generation failed')
    raw = run_lean(A/f'IndependentCheck_{version}.lean', A/f'independent_check_{version}.log', lib)
    require('LB12_INDEPENDENT_AUDIT_PASSED' in raw,'Missing success marker')
    require(not re.search(r'\b(error|warning):',raw),'Lean diagnostic in accepted audit')
    records, closures, exact = {}, {}, {}
    for line in raw.splitlines():
        for tag, dest, key in [('DECLARATION_JSON ',records,'name'),('CLOSURE_JSON ',closures,'root'),
                                ('EXACT_EXPORT_JSON ',exact,'name')]:
            if tag in line:
                row=json.loads(line.split(tag,1)[1]);require(row[key] not in dest,'Duplicate audit record')
                dest[row[key]]=row
    imported = json.loads(next(x.split('MODULES_JSON ',1)[1] for x in raw.splitlines() if 'MODULES_JSON ' in x))
    generated_inputs = read(A/f'check_inputs_{version}.json')
    require(set(generated_inputs['modules']) == modules, 'Generated source module inventory mismatch')
    require(modules <= set(imported), 'Independent environment omitted a source module')
    require(set(imported) == set(objects), 'Independent imported-object closure differs from clean coordinator audit')
    required=before['required_exports']
    require(len(exact)==len(required)==58,'Incomplete exact export audit')
    ownership=read(R/'OWNERSHIP.json')
    owner_evidence=[]
    for e in required:
        rec=records[e['name']]
        require(rec['kind']=='theorem' and rec['type']==e['type'],'Required theorem type changed')
        directory=ownership[e['lane']]['exclusive_paths'][0].rstrip('/').replace('/','.')
        require(rec['module'].startswith(directory+'.'),'Export declared outside assigned owner module')
        owner_evidence.append({**e,'defining_module':rec['module'],'verified':True})
    for name, rec in records.items():
        require(rec['kind']!='axiom' and set(rec['axioms'])<=ALLOWED,'Unexpected axiom '+name)
    require(len(closures)==4,'Missing endpoint root')
    for name, rec in closures.items():
        require(set(rec['recursive_axioms'])==set(rec['collect_axioms'])<=ALLOWED,'Axiom traversal mismatch')
        require(rec['reachable_count']==len(set(rec['all_reachable_names'])),'Invalid closure count')
    for suffix, expected in [('EmpiricalLower.empiricalCombined',False),('EmpiricalLower.coldOnly',False),
                              ('MacroscopicLower.macroscopicIntegrable',True)]:
        actual='RiffleLowerV2.ScalarIntegrable' in closures['RiffleLowerV2.'+suffix]['all_reachable_names']
        require(actual==expected,'Scalar-integrability scope mismatch')
    foundation=read(R/'audit/LB00/compiled-declarations.json')
    for name, old in foundation.items():
        require(name in records,'Frozen foundation declaration missing')
        for field in ['kind','type','type_dependencies','value_dependencies']:
            require(old[field]==records[name][field], 'Frozen compiled declaration changed '+name+' '+field)
    # A separate environment imports only Completed, so direct all-module imports
    # cannot accidentally mask a missing umbrella edge.
    pairs=',\n    '.join('(`'+e['name']+', `'+e['type']+')' for e in required)
    umbrella='''import RiffleLowerV2.Completed
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, target) in #[PAIRS] do
    let some ci := env.find? name | throwError "Missing completed-umbrella export {name}"
    unless ci.isTheorem && ci.type.isConstOf target do
      throwError "Wrong completed-umbrella export {name}"
  logInfo m!"UMBRELLA_MODULES_JSON {(toJson (env.allImportedModuleNames.map Name.toString)).compress}"
  logInfo "LB12_COMPLETED_UMBRELLA_58_EXPORTS_PASSED"
'''.replace('PAIRS',pairs)
    save(A/f'UmbrellaCheck_{version}.lean',umbrella)
    ulog=run_lean(A/f'UmbrellaCheck_{version}.lean',A/f'umbrella_check_{version}.log',lib)
    require('LB12_COMPLETED_UMBRELLA_58_EXPORTS_PASSED' in ulog,'Umbrella check failed')
    umbrella_modules=json.loads(next(x.split('UMBRELLA_MODULES_JSON ',1)[1] for x in ulog.splitlines() if 'UMBRELLA_MODULES_JSON ' in x))
    for row in ownership.values():
        if row.get('required_exports'):require(row['proof_entry_point'] in umbrella_modules,'Missing lane umbrella import')
    save(A/f'compiled_declarations_{version}.json',records)
    save(A/f'endpoint_closures_{version}.json',closures)
    save(A/f'export_ledger_{version}.json',owner_evidence)
    save(A/f'module_graph_{version}.json',{n:{'source':e['path'],'imports':e['imports']} for n,e in before['modules'].items()} |
         {'RiffleLowerV2.Completed':{'source':'RiffleLowerV2/Completed.lean','imports':ownership and
           [x.split()[1] for x in (R/'RiffleLowerV2/Completed.lean').read_text().splitlines() if x.startswith('import ')]}})
    lines=['# LB12 exact checked exports','', 'Every row below is a theorem of its immutable target; target bodies are printed from the same compiled environment.','']
    for e in owner_evidence:
        target=records[e['type']]
        lines += ['## '+e['name'],'', 'Owner: '+e['lane']+'. Defining module: `'+e['defining_module']+'`. Source labels: '+', '.join('`'+s+'`' for s in e['source_labels'])+'.',
          '', '```lean',e['name']+' : '+e['type'],'-- Frozen target body:',target['value'],'```','']
    save(A/f'EXPORTS_{version}.md','\n'.join(lines))
    verify_objects()
    check_hashes(W,before['protected_old_files']);check_hashes(R,before['frozen_files']);check_hashes(R,snapshot)
    summary={'status':'INDEPENDENT_FINAL_AUDIT_PASSED','version':version,'E':'PASS','M':'PASS_WITH_EXPLICIT_SCALAR_INTEGRABILITY',
        'original_arbitrary_TimeLaw':'NOT_CERTIFIED; removing ScalarIntegrable from M is mathematically false under totalized integrals',
        'coordinator_build_evidence':evidence_rel,'coordinator_manifest_sha256':sha(evidence/'SHA256.json'),
        'clean_output':str(lib),'compiler_sha256':sha(COMPILER),'compiler':verification['compiler'],
        'mathlib_commit':verification['mathlib_commit'],'package_modules':len(modules),
        'freshly_built_modules':len(provenance['built']),'declarations_audited':len(records),
        'required_exports':len(exact),'imported_modules':len(imported),'foundation_declarations_unchanged':len(foundation),
        'protected_old_files_unchanged':len(before['protected_old_files']),'imported_object_fingerprints_checked':object_count,
        'axiom_union':sorted({a for row in records.values() for a in row['axioms']}),
        'closure_counts':{n:r['reachable_count'] for n,r in closures.items()},
        'closure_method':'private environment, recursive ConstantInfo.getUsedConstantsAsSet (type/value/inductive/recursor metadata), compared with Lean.collectAxioms',
        'completed_umbrella_exports_checked':58,'unresolved_E_M_obligations':[]}
    save(A/f'VERIFICATION_{version}.json',summary)
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
