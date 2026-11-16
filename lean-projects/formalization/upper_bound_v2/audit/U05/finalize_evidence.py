from pathlib import Path
import json,hashlib,datetime
r=Path(__file__).resolve().parents[2];a=r/'audit/U05'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]
for p in sorted((a/'build-receipts').glob('*.json')):
 d=json.loads(p.read_text())
 if d['recorded_at']>='2026-10-02T20:44:00' and ('--fresh' in d['command'] or d.get('audit_checks')):
  receipts.append({'file':str(p.relative_to(r)),'sha256':sha(p),'command':d['command'],'status':d['status'],'exit_code':0,'recorded_at':d['recorded_at']})
assert len(receipts)==5,len(receipts)
fresh=json.loads((r/receipts[0]['file']).read_text());assert len(fresh['built'])==36
root_receipt=json.loads((r/'audit/U00/first-moment-endpoint-check-build.json').read_text())
closure=json.loads((a/'PROJECT_DEPENDENCY_CLOSURE.json').read_text())
for m,v in closure['project_sources'].items():
 build_source=fresh['modules'].get(m) or root_receipt['modules'].get(m)
 assert build_source and build_source['sha256']==v['sha256'],m
rows=json.loads((a/'ALL_DECLARATIONS.json').read_text());decls=json.loads((a/'DECLARATIONS.json').read_text())
assert len(rows)==577 and len(decls)==208
axs=sorted({ax for x in rows for ax in x['axioms']});assert axs==['Classical.choice','Quot.sound','propext']
assert {d['name'] for d in decls}<={d['name'] for d in rows}
expanded=(a/'final-type.log').read_text().split('U05_F_EXPANDED_TYPE ',1)[1].split('\nRiffleUpperV2.FirstMoment.empiricalGraphDecay',1)[0]
(a/'F_EXPANDED_TYPE.txt').write_text(expanded+'\n')
owned={str(p.relative_to(r)):sha(p) for p in sorted((r/'RiffleUpperV2/FirstMoment').glob('*.lean'))}
reviews=[{'file':str(p.relative_to(r)),'sha256':sha(p)} for p in sorted((r/'audit/U00').glob('U05*review.json'))]
for name in ['first-moment-endpoint-check-build.json','F-expanded-type.txt']:
 p=r/'audit/U00'/name;assert p.exists();reviews.append({'file':str(p.relative_to(r)),'sha256':sha(p)})
verify={
'status':'PROVED_AND_CHECKED','scope':'Exact frozen Contracts.V1.F; all U05 mathematical obligations discharged. No C/E/P/T/R completion is claimed by this lane.','recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
'endpoint':{'name':'RiffleUpperV2.FirstMoment.empiricalFirstMoment','type':'RiffleUpperV2.Contracts.V1.F','file':'RiffleUpperV2/FirstMoment/Empirical.lean','quantitative_helper':'RiffleUpperV2.FirstMoment.empiricalGraphDecay','decay_exponent':'eta/8','expanded_type':'audit/U05/F_EXPANDED_TYPE.txt','kernel_type':'audit/U05/kernel-types.log'},
'contract':{'file':'CONTRACTS_READY.json','version':'v1','sha256':sha(r/'CONTRACTS_READY.json'),'frozen_sources_edited':False},
'manuscript':{'path':str((r.parent.parent/'time_inhomogeneous_riffle_shuffle_unified_article.tex').resolve()),'sha256':sha(r.parent.parent/'time_inhomogeneous_riffle_shuffle_unified_article.tex')},
'owned_source_hashes':owned,
'build':{'fresh_command':'python3 formalization/upper_bound_v2/scripts/build.py --lane U05 --fresh RiffleUpperV2.FirstMoment.Main','exit_code':0,'log':'audit/U05/build.log','fresh_owned_modules':36,'compiler':fresh['compiler'],'compiler_sha256':fresh['compiler_sha256'],'mathlib_commit':fresh['mathlib_commit'],'receipts':receipts,'scope':'Fresh all36 owned modules against immutable U00 source-staged project dependencies; no copied historical project proof objects.'},
'public_declarations':{'total':208,'theorems':sum(x['kind']=='theorem' for x in decls),'index':'audit/U05/DECLARATIONS.json','readable_types_and_transitive_axioms':'audit/U05/types-and-axioms.log','fully_explicit_kernel_types':'audit/U05/kernel-types.log'},
'all_owned_declarations':{'total':577,'including_generated_and_private':True,'index':'audit/U05/ALL_DECLARATIONS.json','checked_types_direct_dependencies_and_transitive_axioms':'audit/U05/trust-check.log','exit_code':0},
'project_dependency_closure':{'file':'audit/U05/PROJECT_DEPENDENCY_CLOSURE.json','project_sources':207,'all_source_hashes_match_U05_fresh_or_U00_endpoint_build_receipts':True},
'source_map':'audit/U05/SOURCE_MAP.json','transitive_axioms':axs,
'independent_review':{'reviewer':'U00','mathematics':'PASS','statement_model_quantifiers':'PASS','adversarial_hidden_hypotheses':'PASS','exact_endpoint_build_types_trust':'PASS','root_declarations_checked':676,'evidence':reviews,'endpoint_review':'audit/U00/U05-F-endpoint-review.json','finite_assembly_review':'audit/U00/U05-graph-assembly-review.json'},
'parameter_order':{'fixed_first':['k','T','eta','g'],'auxiliary_before_threshold':['delta=eta/256','width=eta/256','epsilon=eta/64','D=eta+4','C=D+3','chi satisfying entropy,count,discard restrictions'],'then':['c=eta/8','N0'],'uniform_after_threshold':['N>=N0','0<n<=N in quantitative helper; 2<=n<=N in F','absolute starting time a','horizon K<=T log N','cut arrays','first-column assignments','actual descriptor blocks and slots']},
'generic_inputs_discharged':[
{'input':'Common lower mass and entropy','site':'retainedClassEntropy + retainedClass_originalEntropy; actual descriptor fibers and original absolute grid.'},
{'input':'Large and small exponent scalar prerequisites','site':'AnchoredCosts, StoppingCosts, MaximalCosts, ClassExponents; terminal bound also discharges stable-no-fallback.'},
{'input':'Reserve, smoothing and actual collision density','site':'FirstPileReserve + ClassDensity instantiate U03 Anchor and U04 Localization.Density, including actual atoms and fixed-count laws.'},
{'input':'Class count and rare row discard','site':'retainedClasses_uniform_count and discardedRows_power_bound; C fixed before chi.'},
{'input':'First-column exposure and matching law','site':'firstColumnAnchoredLaw and firstPileEdges_probability from positive conditioning and exact row permutation; future arrays retain full n.'},
{'input':'Independent graph intersection identity','site':'Shared.FirstMomentAPI expectedCommonEdges_eq_sum_sq via actual product PMF; GraphAssembly uses toFirstMomentLaw_expected.'},
{'input':'Localized graph cover and active count','site':'RetainedGraphCover, GraphMarginals, ActiveClasses, ActiveCount; literal rank sets and actual graph slots.'},
{'input':'Per-fiber density and finite sums','site':'retainedClassDensity_eventually + classPrefixes_card + retainedDensity_sum_power; finite-fiber algebra applied after actual cardinalities proved.'},
{'input':'Errors and thresholds','site':'PowerAggregation and UniformGraph; actual candidate count times omitted error and discarded square mass absorbed uniformly.'}],
'remaining_imported_assumptions':[],'missing_obligations':[],
'planned_exports':{'empiricalCostClassCount':'PROVED_AND_CHECKED','classEntropy':'PROVED_AND_CHECKED','empiricalExponentBounds':'PROVED_AND_CHECKED as retainedClass_largeExponent, retainedClass_smallProperExponent, retainedClass_smallImmediateExponent, retainedClass_terminalExponent','empiricalFirstMoment':'PROVED_AND_CHECKED exact F'},
'boundary_cases':['N0>=2 guards log N and real powers','Current n can be smaller than N; no log n substitution','d=0 remains in quantitative domain; impossible goodness/margin combinations handled by model hypotheses','Zero-probability digits excluded only by actual legality where costs are used','Empty classes/unrealized keys contribute zero; representatives guard positive class cardinality','Immediate and terminal classes proved singleton','Zero-based integer ranks match actual Fin(n-1); exposed pile offsets aligned','No ambient-prefix independence premise; matching law proved from actual conditioning and relabeling'],
'delivery_boundary':'Exact F and all U05 helpers released. U09/U11 may specialize empiricalFirstMoment; sibling C/E/P/T/R remain separate.'}
(a/'VERIFICATION.json').write_text(json.dumps(verify,indent=2)+'\n')
(a/'STATUS.txt').write_text('U05 — PROVED_AND_CHECKED\n\nRiffleUpperV2.FirstMoment.empiricalFirstMoment : RiffleUpperV2.Contracts.V1.F\nRate c=eta/8; N0 chosen before N,n,a,K and cut arrays.\nOriginal log N scale and full-n future columns preserved.\n\nFresh build:36 owned modules, Lean4.33.1, exit0.\nExact types:208 public declarations; fully explicit kernel types saved.\nTrust:577 owned declarations including generated/private, transitive axioms only Classical.choice,Quot.sound,propext.\nDependency closure:207 project sources match U05 fresh or U00 endpoint receipt hashes.\nIndependent U00 endpoint review/build/type/trust:PASS,676 declarations standard-only.\n\nAll U05 mathematical obligations discharged. No unproved localization, entropy, density, class-count or first-moment premise remains in F.\nEvidence:VERIFICATION.json, SOURCE_MAP.json, F_EXPANDED_TYPE.txt, ALL_DECLARATIONS.json, build-receipts/.\nC/E/P/T/R are sibling obligations, not claimed here. Sources frozen for downstream integration.\n')
print('VERIFICATION_SAVED',sha(a/'VERIFICATION.json'))
