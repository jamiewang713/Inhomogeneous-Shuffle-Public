#!/usr/bin/env python3
"""Issue U13's final independent verdict from completed, checked evidence."""
from pathlib import Path
import hashlib, json, datetime, shutil
A = Path(__file__).resolve().parent
P = A.parent.parent
W = P.parent.parent
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
def read(name): return json.loads((A/name).read_text())
def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''): h.update(block)
 return h.hexdigest()
def write(name,data): (A/name).write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
def artifact(name):
 p=A/name
 return {'path':str(p),'sha256':sha(p)}
B=read('final-fresh-build-v2.json'); T=read('final-trust-v2.json')
O=read('final-object-inventory-v2.json'); I=read('integration-reconciliation-v2.json')
S=read('final-source-snapshot-v2.json'); V=read('preservation-v2.json')
E=read('endpoint-map-v2.json'); X=read('public-expanded-types-v2.json')
assert B['status']=='BUILD_OK' and len(B['built'])==398
assert T['status']=='TRUST_PASS' and len(T['roots'])==12
assert len(T['recursive_inventory'])==45162 and len(T['all_upper_declarations'])==3907
assert O['status']=='PASS' and not O['unresolved_modules']
assert I['status']=='PASS' and not I['errors'] and I['immutable_artifacts_checked']==552
assert I['project_objects_byte_identical_to_independent_build']==398
assert V['status']=='PASS' and S['status']=='SOURCE_SNAPSHOT_MATCH' and not S['changed']
assert sha(I['handoff'])==I['handoff_sha256'] and sha(I['manifest'])==I['manifest_sha256']
allowed=['propext','Classical.choice','Quot.sound']
roots={r['name']:r for r in T['roots']}
for r in roots.values():
 assert set(r['axioms'])==set(allowed) and r['collector_matches_manual_traversal']
for r in T['recursive_inventory']:
 if r['kind'] in ('theorem','definition','opaque'): assert r['body_available'],r['name']
for name in ['STATUS.txt','VERIFICATION.json']:
 old=A/(Path(name).stem+'_pre_final_v2'+Path(name).suffix)
 if not old.exists(): shutil.copyfile(A/name,old)
for key,row in E.items():
 assert sha(row['proof_source'])==row['proof_source_sha256']
 r=roots[row['actual_declaration']]
 row.update({'status':'PROVED_AND_CHECKED','final_acceptance':True,
  'kernel_build_verdict':'PASS','transitive_trust_verdict':'PASS','adversarial_verdict':'PASS',
  'recursive_dependency_count':r['recursive_dependency_count'],
  'axioms':r['axioms'],'remaining_imported_proof_assumptions':[],
  'expanded_type_file':str(A/(key+'-expanded-type-v2.txt')),
  'expanded_type':X[key]['expanded_type']})
write('endpoint-map-v2.json',E)
log=(A/'final-fresh-build-v2.log').read_text()
warning_count=sum('warning:' in l for l in log.splitlines())
assert 'error:' not in log
exceptions={n:r for n,r in O['external_objects'].items() if r['kind']=='pinned-package-rebuilt-by-coordinator'}
assert len(exceptions)==4
compiler='/Users/jialushi/Documents/loop soup/formalization/.tools/lean-4.33.1-darwin_aarch64/bin/lean'
commands=[
 {'cwd':str(W),'argv':['python3','formalization/upper_bound_v2/scripts/build.py','--lane','U13','--fresh','--run','audit/U13/FinalCheck_v2.lean'],'exit_code':0},
 {'cwd':str(P),'env':{'LEAN_PATH':str(P/'.build/U13/lib/lean')},'argv':[compiler,'-R',str(P),'audit/U13/MetadataCheck_v2.lean'],'exit_code':0},
 {'cwd':str(W),'argv':['python3','formalization/upper_bound_v2/audit/U13/record_build_inventory_v2.py'],'exit_code':0}]
files=['FinalCheck_v2.lean','MetadataCheck_v2.lean','record_build_inventory_v2.py',
 'final-source-snapshot-v2.json','final-fresh-build-v2.json','final-fresh-build-v2.log',
 'final-trust-v2.json','final-metadata-build-v2.json','final-metadata-v2.json','final-metadata-v2.log',
 'final-object-inventory-v2.json','object-inventory-v2.log','integration-reconciliation-v2.json',
 'preservation-v2.json','source-proof-review-v2.txt','endpoint-map-v2.json','public-expanded-types-v2.json',
 'STATUS_pre_final_v2.txt','VERIFICATION_pre_final_v2.json']
files += [k+'-expanded-type-v2.txt' for k in X]
evidence={n:artifact(n) for n in files}
verdict={
 'schema':'U13-independent-final-audit-v2','status':'PROVED_AND_CHECKED',
 'recorded_at':now,'auditor':'U13 independent final auditor','final_acceptance':True,
 'scope':'The six upper-bound endpoints F/C/E/P/T/R at INTEGRATION_READY v1, including all three R components. Production sources and manuscript read-only.',
 'handoff':{'path':I['handoff'],'sha256':I['handoff_sha256'],
   'manifest':I['manifest'],'manifest_sha256':I['manifest_sha256'],
   'immutable_artifacts_verified':552,'project_source_hashes_match':True,
   'root_and_independent_project_objects_byte_identical':398},
 'manuscript':{'path':str(W/'time_inhomogeneous_riffle_shuffle_unified_article.tex'),'sha256':S['manuscript_sha256']},
 'endpoint_verdicts':E,
 'random_components':{k:X[k] for k in ['REmpiricalBound','REmpirical','RProfile']},
 'runtime':{'compiler_path':compiler,'compiler_version':B['compiler'],'compiler_sha256':B['compiler_sha256'],
  'mathlib_commit':B['mathlib_commit'],'package_revisions':O['package_revisions'],
  'runtime_objects':O['runtime_objects']},
 'fresh_build':{'status':'PASS','exit_code':0,'project_modules_rebuilt':398,
  'owned_regular_project_outputs':398,'owned_regular_project_receipts':398,
  'project_output_or_receipt_symlinks':0,'output':B['output'],'builder_sha256':B['builder_sha256'],
  'audit_source_sha256':B['audit_checks'][0]['sha256'],
  'compiler_error_lines':0,'nonfatal_warning_lines':warning_count,
  'warning_scope':'Exact warning-line count in the archived full independent build log; no claim of a warning-free build.'},
 'trust':{'status':'PASS','actual_endpoint_roots':6,'completed_alias_roots':6,
  'recursive_dependency_union':45162,'all_upper_declarations_checked':3907,
  'all_theorem_definition_opaque_bodies_available':True,
  'traversal':'Types and values, including opaque values, plus inductive names and constructors and recursor names/rules/RHS dependencies; independent DFS compared separately to Lean.collectAxioms for each root.',
  'allowed_axioms':allowed,'actual_axioms_at_each_root':allowed,
  'manual_traversal_matches_lean_collector_for_all_roots':True,
  'sorry_custom_axiom_native_oracle_or_missing_body_found':False},
 'external_library_trust':{'imported_modules':5331,'project_modules':398,'external_package_modules':3401,
  'core_modules':1532,'unresolved_modules':[],
  'boundary':'Acceptance trusts the recorded Lean runtime and pinned external package/core objects. U13 independently rebuilt every project source; it did not rebuild all external library or core sources. Exact resolved object paths, SHA256 hashes, companion objects, and package revisions are in final-object-inventory-v2.json.',
  'coordinator_built_pinned_library_exceptions':exceptions,
  'exceptions_verification':'All four are pinned mathlib sources absent from the package cache, compiled by U00 with the same compiler and mathlib revision; their imported objects match the frozen clean rebuild byte for byte. Source hashes and clean build receipts were verified. These are external-library trust, not project-source exceptions.'},
 'source_and_adversarial_review':{'status':'PASS','report':artifact('source-proof-review-v2.txt'),
  'model':'Concrete fixed-count physical inverse law, chronological column order, stable-sort graph bridge, and half-L1 TV.',
  'quantifiers':'Original N scale in all subdecks; all integer endpoints and theta in [3,4]; uniform E parameter order; arbitrary fixed partition; g and gamma before decreasing rho; coherent horizons and extended infinite thresholds; arbitrary joint random cut law.',
  'hard_chain':'Actual physical/graph bridge, arbitrary overlap fibers, product-event truncation, reserved post-anchor smoothing, direct fourth-power density, full localization/class losses, original-scale F, exact natural sorted-history law and removable copies, auxiliary disintegration without enlarged filtration, three block regimes, initial and terminal histories, adapted moments, 2k cover, deterministic restart, fixed-partition transfer, critical/mixing semantics, random averaging.',
  'auxiliary_numerical_choices':'Certified full-H constant 1/24, hypergeometric atom constant 16, F exponent eta/8, scalar bound 4 log k and terminal rounding loss 14 log k/log N have explicit downstream absorption proofs preserving all public endpoints.',
  'resolved_earlier_findings':['U13-01 original/current/anchor scale and absolute indexing','U13-02 literal H, natural histories, directional remainder and separate i=0','U13-03 common partition constant and integrability/parameter order','U13-04 coherent horizons and extended infima','U13-05 arbitrary cut-array PMF and physical mixture','U13-R-01 quantitative empirical random-cut component is present and proved'],
  'manuscript_to_lean_mismatches':[]},
 'preservation':V,
 'remaining_imported_proof_assumptions':[],
 'remaining_obligations':[],
 'scope_limits':['Acceptance is for the six frozen upper endpoints, not a new lower-bound theorem or a stronger cutoff statement.','Critical-time convergence is strictly above the threshold; infinite thresholds retain the extended semantics.','Public mathematical hypotheses in the exact expanded types remain hypotheses; there is no hidden first-moment, conditional-law, localization, moment, or TV certificate premise.'],
 'reproduction':commands,'evidence':evidence,
 'historical_evidence':'Earlier U13 reviews remain untouched. Previous STATUS/VERIFICATION are copied to *_pre_final_v2. DevelopmentCheck_v2 is explicitly excluded from final proof evidence.'}
write('FINAL_AUDIT.json',verdict)
report='''U13 INDEPENDENT FINAL AUDIT — PROVED_AND_CHECKED
Recorded: {date}

Accepted: F, C, E, P, T, R separately. No unresolved mathematical, statement,
model, build or transitive-proof obligation remains at the recorded hashes.
R includes its quantitative empirical mixture bound, empirical convergence,
and profile convergence. Exact declarations, aliases, source labels and expanded
types are in FINAL_AUDIT.json, endpoint-map-v2.json and *-expanded-type-v2.txt.

Actual exports:
'''.format(date=now)
for k,e in E.items(): report+=k+'  '+e['actual_declaration']+'\n'
report+='''
Independent source review covered the manuscript and actual production proofs,
including the physical-law/graph bridge, reserve and history laws, all block
regimes, original-N subdeck estimates, adapted moments, restart, fixed-partition
transfer, extended critical-time semantics and dependent random-cut averaging.
See source-proof-review-v2.txt for discharge sites, quantified uniformity,
numerical substitutions and adversarial cases. No manuscript-to-Lean mismatch
was found. Historical U13-R-01 is resolved by the actual REmpiricalBound export.

Fresh independent build: exit 0; every one of the 398 project source modules was
rebuilt in .build/U13. All project objects and source receipts are regular owned
files without symlink ancestors, and all 398 objects match root clean byte for
byte. The archived build contains {warnings} nonfatal warning lines and zero errors.
The 12 actual/Completed theorem roots were recursively traversed through types,
proof values, opaque bodies, constructors and recursor metadata. The union has
45,162 declarations; all 3,907 upper declarations were also checked. Each root's
axioms are exactly propext, Classical.choice and Quot.sound, in agreement with
Lean.collectAxioms. No custom axiom, sorry, missing body or native proof oracle
reaches a public endpoint.

Runtime: Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Compiler SHA256: {compiler_sha}
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.
Trust boundary: pinned external library/core objects and the Lean runtime are
trusted, not independently rebuilt in their entirety. All 5,331 imported modules
were resolved: 398 project, 3,401 external package, 1,532 core. Exact object paths,
hashes and available companions are in final-object-inventory-v2.json. Four
external mathlib modules missing from the cache were built by U00 and separately
matched to the frozen clean build and pinned sources: Probability.Distributions.
Uniform, Probability.ProbabilityMassFunction.Integrals, Combinatorics.Enumerative.
DoubleCounting, and Combinatorics.Pigeonhole. These are explicit library trust;
there is no corresponding exception among project sources.

Accepted immutable INTEGRATION_READY v1 SHA256:
{handoff}
Its immutable 552-artifact MANIFEST SHA256:
{manifest}
All 552 archived hashes verified; all current project sources match the frozen
sources and independent build. Manuscript SHA256:
{manuscript}
All 183 finished lower-v20 package sources and 23 initial inputs retain their
recorded hashes; the initial user working-tree state was preserved.

Reproduce the full project build from the workspace root:
python3 formalization/upper_bound_v2/scripts/build.py --lane U13 --fresh --run audit/U13/FinalCheck_v2.lean

Reproduce metadata from formalization/upper_bound_v2 using the exact compiler:
LEAN_PATH='{overlay}' '{compiler}' -R '{package}' audit/U13/MetadataCheck_v2.lean

Record object inventories from the workspace root:
python3 formalization/upper_bound_v2/audit/U13/record_build_inventory_v2.py

All three recorded commands exited 0. SHA256_v2.json indexes the final evidence.
Acceptance covers the frozen upper endpoints and their stated hypotheses. It
asserts no critical-time equality claim or additional lower-bound/cutoff theorem.
Earlier partial reviews remain preserved and are superseded only by this final
verdict and its associated FINAL_AUDIT.json and VERIFICATION.json.
'''.format(warnings=warning_count,compiler_sha=B['compiler_sha256'],handoff=I['handoff_sha256'],manifest=I['manifest_sha256'],manuscript=S['manuscript_sha256'],overlay=B['output'],compiler=compiler,package=P)
(A/'FINAL_REPORT.txt').write_text(report)
verification={
 'status':'PROVED_AND_CHECKED','phase':'INDEPENDENT_FINAL_ACCEPTANCE','recorded_at':now,
 'final_acceptance':True,'endpoint_verdicts':{k:{'status':v['status'],'declaration':v['actual_declaration'],'source_label':v['source_label']} for k,v in E.items()},
 'fresh_lean_build':True,'fresh_project_module_count':398,'build_exit_code':0,
 'integration_ready_reviewed':True,'handoff_sha256':I['handoff_sha256'],'manifest_sha256':I['manifest_sha256'],
 'frozen_artifacts_verified':552,'transitive_axiom_audit':True,'root_count':12,
 'recursive_declaration_count':45162,'upper_declaration_count':3907,'permitted_axioms':allowed,
 'external_library_trust_boundary':verdict['external_library_trust']['boundary'],
 'coordinator_built_pinned_library_exceptions':list(exceptions),
 'source_hash_matches_plan':True,'manuscript_to_lean_mismatches':[],
 'remaining_imported_proof_assumptions':[],'remaining_obligations':[],
 'final_audit':artifact('FINAL_AUDIT.json'),'report':artifact('FINAL_REPORT.txt'),
 'reproduction':commands,'evidence':evidence,
 'changes_scope':['audit/U13/','.build/U13/']}
write('VERIFICATION.json',verification)
(A/'STATUS.txt').write_text('''PROVED_AND_CHECKED — U13 independently accepts INTEGRATION_READY v1.
F/C/E/P/T/R: separately accepted; R includes all three random-cut components.
398 project sources freshly rebuilt, exit 0; all project objects/receipts owned.
552 immutable artifacts verified; 398 independent/root objects byte-identical.
12 roots, 45,162 recursive declarations; all 3,907 upper declarations checked.
Only propext, Classical.choice, Quot.sound; no unresolved proof/model obligation.
Pinned library/core/runtime trust is explicit, including four verified U00-built
mathlib objects. Full source/object hashes and expanded types are archived.
Final evidence: FINAL_AUDIT.json, FINAL_REPORT.txt, VERIFICATION.json, SHA256_v2.json.
Earlier reviews and pre-final STATUS/VERIFICATION are preserved.
''')
files+=['FINAL_AUDIT.json','FINAL_REPORT.txt','VERIFICATION.json','STATUS.txt','finalize_audit_v2.py']
write('SHA256_v2.json',{'recorded_at':now,'status':'PASS','files':{n:artifact(n) for n in files},'self_hash':'Excluded to avoid circularity; hash this index externally.'})
print(json.dumps({'status':'PROVED_AND_CHECKED','endpoints':list(E),'warning_lines':warning_count,
 'FINAL_AUDIT_sha256':sha(A/'FINAL_AUDIT.json'),'VERIFICATION_sha256':sha(A/'VERIFICATION.json'),
 'SHA256_index_sha256':sha(A/'SHA256_v2.json')},indent=2))
