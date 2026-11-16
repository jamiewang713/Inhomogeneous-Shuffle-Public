"""Create a lane-only release receipt from checked Lean declarations."""
from pathlib import Path
import datetime,hashlib,json,re
ROOT=Path(__file__).resolve().parents[2]
WORK=ROOT.parents[1]
OUT=ROOT/'audit/LB02'
LOG=OUT/'final_build_and_axioms_v1.log'
for name in ['compiled_declarations_v1.json','obligations_final_v1.json',
             'EXPORTS_v1.md','LB02_READY_v1.json','DELIVERY_v1.md']:
    assert not (OUT/name).exists(), f'Refusing to overwrite existing release artifact: {name}'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
log=LOG.read_text()
assert log.rstrip().endswith('LB02 BUILD_OK'), 'Final lane check has not succeeded'
assert not re.search(r'\berror:',log), 'Lean diagnostic error'
assert (OUT/'final_readiness_v1.log').read_text().strip()=='LB02 CONTRACT_INPUTS_OK'
decls=[]
for line in log.splitlines():
    if 'LB02_DECLARATION_JSON ' in line:
        decls.append(json.loads(line.split('LB02_DECLARATION_JSON ',1)[1]))
assert decls, 'No compiled declaration inventory'
byname={d['name']:d for d in decls}
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(d['axioms'])<=allowed for d in decls)
frozen=json.loads((ROOT/'OWNERSHIP.json').read_text())['LB02']['required_exports']
for d in frozen:
    assert d['name'] in byname, d['name']
    assert byname[d['name']]['kind']=='theorem'
    assert byname[d['name']]['type']==d['type'], (d,byname[d['name']]['type'])
extra=['Compat.HypergeomParams.expect_pow_le_all','Compat.sample_expect_pow_intersection_le',
 'permutation_subset_expect','permutation_intersection_transform','column_subset_expect',
 'column_intersection_transform','independent_intersection_transform','thinningTails',
 'prefixTransform','prefixCount_eq_zero_of_mass_zero','residualConditionalExpect',
 'residualConditionalProbability','residualColumnIndependence','residualPrefixCount_eq_restriction',
 'residualPrefixMass_eq','residualPrefixMean_eq','residualPrefixTransform','residualPrefixTails',
 'maximalWordTail','chernoffConstant_pos','prefix_card_exact','prefix_card_le_of_cuts',
 'prefixFailure_le_envelope','prefixFailureEnvelope_tendsto']
extra=['RiffleLowerV2.Thinning.'+n for n in extra]
for n in extra:assert n in byname and byname[n]['kind']=='theorem',n
sources={str(p.relative_to(ROOT)):sha(p) for p in sorted((ROOT/'RiffleLowerV2/Thinning').rglob('*.lean'))}
for rel in sources:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',(ROOT/rel).read_text()),rel
manifest=ROOT/'Contracts/v1/SHA256.json'
for rel,h in json.loads(manifest.read_text()).items():assert sha(ROOT/rel)==h,rel
for rel,h in json.loads((ROOT/'Contracts/v1/SOURCES.json').read_text())['external_files'].items():assert sha(WORK/rel)==h,rel
for rel,d in json.loads((OUT/'compat_provenance_v1.json').read_text()).items():
    assert sha(WORK/rel)==d['original_sha256'],rel
# The initial provenance snapshot predates documented compiler compatibility fixes.
# Validate final ports against the later successful compatibility-build receipt;
# retain both historical records unchanged.
for rel,d in json.loads((OUT/'compat_receipt_v1.json').read_text())['ports'].items():
    assert sha(WORK/rel)==d['original_sha256'],rel
    assert sha(WORK/d['port'])==d['port_sha256'],d['port']
reviews=['math_review_v1.md','representation_review_v1.md','hypotheses_review_v1.md',
 'review_resolution_v1.md','analytic_independent_review_v1.md','integration_independent_review_v1.md',
 'final_hypotheses_review_v1.md','compat_final_provenance_review_v1.md']
for r in reviews:assert (OUT/r).is_file(),r
obligations=[
 ('1','lem:successive-thinning-tail','All positive s under the exact uniform-permutation hypergeometric law', ['hypergeometricTransform','Compat.HypergeomParams.expect_pow_le_all','permutation_subset_expect']),
 ('2','lem:successive-thinning-tail','Independent subset process via exact finite coordinate integration and backward affine recursion', ['successiveThinning','independent_intersection_transform','permutation_intersection_transform']),
 ('3','lem:successive-thinning-tail','Exact Bernstein, half-mean and fewer-than-two tails; positive population, zero mean and empty columns included', ['thinningTails','prefixTails','chernoffConstant_pos']),
 ('4','lem:successive-thinning-tail','Actual admissible residual law, subtracted counts, independent residual columns and concrete residual transform/tails', ['residualLaw','residualColumnIndependence','residualPrefixTransform','residualPrefixTails']),
 ('5a','cor:iterated-hypergeom','Actual prefix law bridge and explicit simultaneous polynomial union bound over every length', ['prefixTransform','allPrefixConcentration','prefix_card_exact','prefix_card_le_of_cuts','prefixCount_eq_zero_of_mass_zero']),
 ('5b','cor:iterated-hypergeom','Uniform convergence with k,T,epsilon,delta before N0, then every N,K satisfying K<=T log N', ['prefixFailureUniform','prefixFailure_le_envelope','prefixFailureEnvelope_tendsto']),
 ('6','prop:largest-prefix','Canonical deterministic maximal word, exact maximal mean/exponent and exponential count tail for LB10', ['maximalMeanIdentity','maximalWordTail'])]
ledger=[]
for item,label,claim,names in obligations:
    full=['RiffleLowerV2.Thinning.'+n for n in names]
    assert all(n in byname for n in full)
    ledger.append({'item':item,'source_label':label,'claim':claim,'status':'proved_and_checked','declarations':full})
(OUT/'compiled_declarations_v1.json').write_text(json.dumps(sorted(decls,key=lambda d:d['name']),indent=2)+'\n')
(OUT/'obligations_final_v1.json').write_text(json.dumps({'lane':'LB02','pending':[], 'requirements':ledger,'external_scope':'LB01 physical law and LB10 run/TV assembly are not certified or consumed by this lane.'},indent=2)+'\n')
selected=[d['name'] for d in frozen]+extra
md='# LB02 exact compiled export inventory\n\nAll declarations below are checked theorems in the pinned Lean environment. Frozen target definitions retain the exact bodies in `Contracts/v1/EXPORTS.md`; the seven assignment checks in `Thinning/Check.lean` compile. Every generic input in the concrete exported results is discharged.\n\n'
for n in selected:
    md+='## '+n+'\n\n```lean\n'+n+' :\n'+byname[n]['type']+'\n```\n\n'
(OUT/'EXPORTS_v1.md').write_text(md)
receipt={'lane':'LB02','status':'COMPLETE','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'entry_point':'RiffleLowerV2.Thinning.Main','audit_entry_point':'RiffleLowerV2.Thinning.Check',
 'compiler':'Lean 4.33.1','mathlib_commit':'0df444a360eaa60ab8c11dca51a86af692955474',
 'contract_manifest_sha256':sha(manifest),'source_sha256':sha(WORK/'time_inhomogeneous_riffle_shuffle_unified_article.tex'),
 'build_command':'python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Check',
 'build_log':'audit/LB02/final_build_and_axioms_v1.log','build_log_sha256':sha(LOG),
 'readiness_log':'audit/LB02/final_readiness_v1.log',
 'readiness_log_sha256':sha(OUT/'final_readiness_v1.log'),
 'checked_compatibility_provenance':'audit/LB02/compat_receipt_v1.json',
 'checked_compatibility_provenance_sha256':sha(OUT/'compat_receipt_v1.json'),
 'decl_count':len(decls),'public_theorem_count':sum(d['kind']=='theorem' and not d['name'].startswith('_private.') for d in decls),
 'axiom_union':sorted(set().union(*(set(d['axioms']) for d in decls))),
 'required_exports':[{**d,'status':'PROVED','axioms':byname[d['name']]['axioms']} for d in frozen],
 'additional_required_exports':extra,'sources':sources,'reviews':{r:sha(OUT/r) for r in reviews},
 'declaration_inventory_sha256':sha(OUT/'compiled_declarations_v1.json'),
 'obligation_ledger_sha256':sha(OUT/'obligations_final_v1.json'),
 'export_inventory_sha256':sha(OUT/'EXPORTS_v1.md'),
 'pending_lane_obligations':[], 'downstream_import':'RiffleLowerV2.Thinning.Main',
 'compiled_overlay':'.build/lanes/LB02/lib/lean','scope':'Concrete count concentration only; no physical permutation-law or TV theorem is asserted.'}
(OUT/'LB02_READY_v1.json').write_text(json.dumps(receipt,indent=2)+'\n')
lines=['# LB02 delivery and import receipt v1','','**LB02 is complete against the unchanged frozen v1 targets.** All seven required declarations and the prompt-required concrete specializations compile.','',
 'The manuscript, original packages, shared sources, package configuration, umbrella imports, and historical freezes were preserved. This receipt certifies concentration of actual matrix counts; it makes no permutation/run/TV claim.','',
 '## Required frozen declarations','', '| Declaration in `RiffleLowerV2.Thinning` | Exact type | Status |','| --- | --- | --- |']
for d in frozen:lines.append('| `'+d['name'].rsplit('.',1)[1]+'` | `'+d['type']+'` | proved |')
lines+=['','`EXPORTS_v1.md` prints the exact compiled types of these and all additional delivery exports. `compiled_declarations_v1.json` records every elaborated lane declaration, its type/body dependencies, and its closure.','','## Source correspondence and proof ledger','','| Source | Completed obligation | Evidence |','| --- | --- | --- |']
for item,label,claim,names in obligations:lines.append('| `'+label+'` | '+claim+' | '+', '.join('`'+n+'`' for n in names)+' |')
lines+=['','There are no pending LB02 proof dependencies. LB00 is the sole required upstream lane and its immutable receipt/hash check passed. LB01 law identification and LB10 permutation/run/TV assembly are outside this certificate and are not assumed here. No pending target proposition is used as evidence.','','## Verification','','Run from `formalization/lower_bound_v2`:','','```text','python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Main','python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Check','python3 scripts/lane.py LB02 --check-ready','```','','`main_build_v2.log` records the successful complete main entry build before the final additive residual-factorization import. `final_build_and_axioms_v1.log` rebuilds the final Main and all transitive owned modules, checks exact membership in all seven frozen target types, audits the complete lane closure, and ends in `LB02 BUILD_OK`. Development failure logs remain preserved. Only nonfatal style lints from compatibility ports remain.','','The final audit covers '+str(len(decls))+' elaborated declarations. The complete closure is exactly `propext`, `Classical.choice`, and `Quot.sound`. Source scans find no proof placeholders, custom assumptions, or native proof oracles. Lean is 4.33.1 and mathlib is pinned at `0df444a360eaa60ab8c11dca51a86af692955474`.','','## Domains and uniformity','','All-s transforms retain s>0 and the frozen positive-population domain. The proofs include empty columns, zero/full piles, zero means, empty prefixes and zero-mass prefixes. Every finite prefix theorem permits the alphabets allowed by its contract, including k=0/1; the k=0 feasibility case is proved. The simultaneous error is exactly `2*(K+1)*k^K*exp(-N^epsilon/8)`. For fixed k>=2,T>0,epsilon>0,delta>0, N0 precedes all N and all K<=T log N.','','Residual results require b<N, injective prescribed labels and positive prescription probability. The statistic removes prescribed matches and uses the exact reduced mean with population N-b and counts count-used. The factorization theorem handles arbitrary real column tests and every deterministic complement enumeration. The maximal word is selected from the cuts before sampling and before the threshold m; its exponential tail is uniform over this deterministic choice.','','## Independent review and provenance','','The initial mathematical, Lean representation and missing-hypothesis reviews approved the unchanged contract before proofs. `review_resolution_v1.md` records their comparison. Independent analytic and integration reviews checked the finite recursion, tail constants, concrete substitutions and quantifiers. The one integration elaboration finding was resolved by exposing the canonical sample type, then independently checked. `final_hypotheses_review_v1.md` closes the edge-case audit. No mathematical objection remains.','','Compatibility source hashes and signature adaptations are recorded in `compat_provenance_v1.json`, with separate sampling, residual, asymptotic and root proof receipts. Original caches were never imported. New ports and proof files live only under the owned Thinning tree.','','## Downstream handoff','','Import `RiffleLowerV2.Thinning.Main`. Use `LB02_READY_v1.json` for hashes, export names, logs and the import receipt. The checked output is in `.build/lanes/LB02/lib/lean`. Only LB00/the coordinator may publish these sources into the shared compiled overlay or update umbrella imports for downstream lanes; this task has not modified those shared integration files.','']
lines=[line.replace(
 'Compatibility source hashes and signature adaptations are recorded in `compat_provenance_v1.json`,',
 'The initial compatibility provenance remains preserved in `compat_provenance_v1.json`; final checked port hashes and compiler adaptations are recorded in the later `compat_receipt_v1.json` and independently verified in `compat_final_provenance_review_v1.md`,') for line in lines]
(OUT/'DELIVERY_v1.md').write_text('\n'.join(lines))
print(json.dumps({'status':'LB02_READY','declarations':len(decls),'required_exports':len(frozen),'additional_exports':len(extra),'axioms':receipt['axiom_union']}))
