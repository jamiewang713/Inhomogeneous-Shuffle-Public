from pathlib import Path
import json, hashlib, re, datetime
root=Path(__file__).resolve().parents[2]
audit=root/'audit/U08'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
log=(audit/'final-types-and-axioms.log').read_text()
rows=[]
for line in log.splitlines():
    marker='UPPER_DECLARATION_JSON '
    if marker in line:
        rows.append(json.loads(line.split(marker,1)[1]))
m=re.search(r'U08_RESERVOIR_TRUST_OK (\d+)',log)
assert m and int(m.group(1))==len(rows)>0
assert len({r['name'] for r in rows})==len(rows)
assert all(set(r['axioms'])<={'propext','Quot.sound','Classical.choice'} for r in rows)
assert not any(r['kind']=='axiom' for r in rows)
rows.sort(key=lambda r:r['name'])
(audit/'final-declaration-inventory.json').write_text(json.dumps(rows,indent=2)+'\n')
ns='RiffleUpperV2.Reservoir.'
exports=['historyAtom','historyAtom_backward','exactMarkedRowLaw','exactResidualMarkedRowLaw','exactTailResidualMarkedRowLaw','residual_prefixWeight_given_pile','pileBase_tailPrefix_probability','history_denominator_lower_uniform','backward_history_denominator_lower_uniform','prefixCount','extraCurrentCopies','tailCollisions','Backward.prefixCount','Backward.extraCurrentCopies','Backward.tailCollisions','futureCylinderConditionalExpect_forward','futureCylinderConditionalExpect_backward','inducedMatrix_uniform','blockGraph_eq_induced','futureCylinderGraphExpect_forward','futureCylinderGraphExpect_backward','unlabeledCylinderGraphExpect_forward','unlabeledCylinderGraphExpect_backward','conditionalFutureCylinderLaw','conditionalFutureCylinderLaw_unlabeled']
byname={r['name']:r for r in rows}
assert all(ns+n in byname for n in exports), [n for n in exports if ns+n not in byname]
(audit/'public-export-types.json').write_text(json.dumps([byname[ns+n] for n in exports],indent=2)+'\n')
(audit/'declaration-names.json').write_text(json.dumps([r['name'] for r in rows],indent=2)+'\n')
sources=sorted((root/'RiffleUpperV2/Reservoir').glob('*.lean'))
source_hashes={str(p.relative_to(root)):sha(p) for p in sources}
for receipt_name in ['final-fresh-build-receipt.json','final-type-axiom-build-receipt.json']:
    receipt=json.loads((audit/receipt_name).read_text())
    assert receipt['status']=='BUILD_OK', receipt_name
    assert all(v.get('exit_code',0)==0 for v in receipt['modules'].values())
    for source, digest in source_hashes.items():
        module=source[:-5].replace('/','.')
        assert receipt['modules'][module]['sha256']==digest
reviews=sorted((root/'audit/U00').glob('U08-*-review.json'))
review_refs=[{'path':str(p.relative_to(root)),'sha256':sha(p),'status':json.loads(p.read_text()).get('status',json.loads(p.read_text()).get('verdict'))} for p in reviews]
source_map=[
 {'source':['eq:ub-exact-history-constraint'],'declarations':['historyAtom','historyAtom_backward','sorted_history_iff','tupleHistoryConstraint_iff','backwardTupleHistoryConstraint_iff'],'status':'PROVED_AND_CHECKED','notes':'Literal frozen naturalHistory, full sorted pile word multiplicities, observed terminal copies; both directions and every nonempty valid reveal length j+1.'},
 {'source':['eq:ub-reservoir-exact-prefix-weight'],'declarations':['exactMarkedRowLaw','exactResidualMarkedRowLaw','exactTailResidualMarkedRowLaw','remainingPopulation_eq','residual_prefixWeight_given_pile','pileBase_tailPrefix_probability'],'status':'PROVED_AND_CHECKED','notes':'Full-pile factorial disintegration, positive exposed-factor cancellation, residual c+m population, first-column cancellation and exact prefix marginal; unused suffix columns are summed out. Impossible allocations and null histories retain zero conventions.'},
 {'source':['lem:ub-reservoir-counts','quantitative reserve denominator'],'declarations':['concentration_remainingCount','reserve_tailWeight_uniform','history_denominator_lower_uniform','backward_history_denominator_lower_uniform'],'status':'PROVED_AND_CHECKED','notes':'Literal H supplies remaining-count bounds. Actual selected right/left reserves remain compatible with the literal history. Exact conditional denominator >= reserveMass^m/2 for m=1,2; constants precede arrays and histories.'},
 {'source':['lem:ub-reservoir-counts','regular and rare coordinates'],'declarations':['regular_coordinate_ratio','rare_coordinate_ratio','coordinate_power_envelope','product_power_envelope','residual_product_upper_uniform'],'status':'PROVED_AND_CHECKED','notes':'Actual residual capacities and population lower bound, falling-factorial domination, rare exponent identity and uniform logarithmic error absorption; zero probabilities included.'},
 {'source':['eq:ub-conditional-cylinder-count'],'declarations':['prefixCount','Backward.prefixCount'],'status':'PROVED_AND_CHECKED','notes':'Natural history only. C1=4/d0, original population n and log n, exact marked-pile support cancellation, one n*epsilon contribution.'},
 {'source':['eq:ub-conditional-extra-copies'],'declarations':['removableCopies','unmarkedHistoryConstraint_of_current_removal','extraCurrentCopies','Backward.extraCurrentCopies'],'status':'PROVED_AND_CHECKED','notes':'Natural-number C_s-t is positive-part excess. Deleting a counted marked row leaves >=t current copies, so observed forced copies are excluded; one bad contribution per row.'},
 {'source':['eq:ub-conditional-tail-collisions'],'declarations':['extensionPowerMass_eq','markedCollision_indicator_partition','tailCollisions','Backward.tailCollisions'],'status':'PROVED_AND_CHECKED','notes':'C2=8/d0^2; exact suffix product with exponent 2(1-alpha). Sum good full-word events before charging one bad event per pair. Ordered pairs conservatively dominate choose2; existential downstream constants unchanged and independently accepted.'},
 {'source':['lem:ub-exact-conditional-block-law'],'declarations':['interiorColumnEquiv','interiorMatrixEquiv','interiorProjectionFibers','futureCylinderConditionalExpect_forward','futureCylinderConditionalExpect_backward','inducedMatrix_uniform','blockGraph_eq_induced','futureCylinderGraphExpect_forward','futureCylinderGraphExpect_backward','unlabeledCylinderGraphExpect_forward','unlabeledCylinderGraphExpect_backward','conditionalFutureCylinderLaw','conditionalFutureCylinderLaw_unlabeled'],'status':'PROVED_AND_CHECKED','notes':'Actual family view Z records natural history, labeled cylinder sets, absolute intervals, induced counts and current-word total. Explicit rectangle replacement bijections preserve every component and give the exact uniform independent-column marginal. Chronological induced Cuts and sorted internal graph are transported exactly. Equal fine-fiber expectations prove label erasure. No independence between distinct cylinders is claimed.'}
]
(audit/'SOURCE_MAP.json').write_text(json.dumps(source_map,indent=2)+'\n')
old=json.loads((audit/'VERIFICATION.json').read_text())
verification={
 'lane':'U08','status':'PROVED_AND_CHECKED','generated_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'frozen_contract_version':'v1','contract_sha256':old['contract_sha256'],'manuscript_sha256':old['manuscript_sha256'],
 'source_sha256':source_hashes,'module':'RiffleUpperV2.Reservoir.Module','source_module_count':len(sources),
 'declarations':[r['name'] for r in rows],'declaration_count':len(rows),'theorem_count':sum(r['kind']=='theorem' for r in rows),
 'all_declaration_types_dependencies_axioms':'audit/U08/final-declaration-inventory.json',
 'public_export_types':'audit/U08/public-export-types.json','public_exports':[ns+n for n in exports],
 'public_planned_exports':{n:'PROVED_AND_CHECKED; backward variants included where applicable' for n in ['historyAtom','exactMarkedRowLaw','prefixCount','extraCurrentCopies','tailCollisions','conditionalFutureCylinderLaw']},
 'build':{'command':'python3 formalization/upper_bound_v2/scripts/build.py --lane U08 --fresh RiffleUpperV2.Reservoir.Module','exit_code':0,'log':'audit/U08/final-fresh-build.log','log_sha256':sha(audit/'final-fresh-build.log'),'receipt':'audit/U08/final-fresh-build-receipt.json','receipt_sha256':sha(audit/'final-fresh-build-receipt.json')},
 'types_and_axioms':{'command':'python3 formalization/upper_bound_v2/scripts/build.py --lane U08 --run audit/U08/FinalCheck.lean','exit_code':0,'log':'audit/U08/final-types-and-axioms.log','log_sha256':sha(audit/'final-types-and-axioms.log'),'receipt':'audit/U08/final-type-axiom-build-receipt.json','receipt_sha256':sha(audit/'final-type-axiom-build-receipt.json'),'checker':'audit/U08/FinalCheck.lean','checker_sha256':sha(audit/'FinalCheck.lean'),'transitive_checks':len(rows),'axioms':['Classical.choice','Quot.sound','propext'],'scope':'All declarations from imported Reservoir modules, including private/generated/definitions; pp.all and pp.universes true for fully explicit types. Lean.collectAxioms checks the full transitive proof closure.'},
 'independent_reviews':review_refs,'review_scope':'U00 independently checked mathematics, actual Lean models/quantifiers, adversarial boundaries, root compilation and standard-only transitive trust across released slices.',
 'source_map':'audit/U08/SOURCE_MAP.json','remaining_obligations':[],
 'upstream_assumptions':[
  {'input':'Actual H concentration and historyGood predicate','provider':'U07, Exploration.UniformConcentration.uniformConcentration','discharge':'concentration_remainingCount supplies deterministic residual counts; NaturalAveraging/BackwardCounts condition only on historyGood, exactly as the source lemma.'},
  {'input':'Actual chosen reserve existence, mass and lexical direction','provider':'U07, chosenReserves_of_retainedGoodCluster, chosenReserves_spec, DirectionalRanks','discharge':'Denominator/BackwardDenominator instantiate actual right/left reserve on hasDirection; no reserve probability premise supplied by callers.'},
  {'input':'Finite exact averaging and product laws','provider':'U00 Shared and U02/LowerV2 checked probability infrastructure','discharge':'Refinement/NaturalAveraging/SupportBridge and FutureCylinderLaw/LabelAveraging discharge support, measurability, count and explicit fiber-equivalence requirements.'}
 ],
 'boundary_conditions':[
  'Source estimates assume a last observed word; public statements use j : Fin pileSize and time j+1. Empty initial piles contain no such history. Time-zero C is an unconditional first-moment branch owned by U09, not a missing source reservoir estimate.',
  'Impossible marked allocations and null intermediate fibers use totalized zero. Actual final family atoms are realized and therefore positive under the finite uniform matrix law.',
  'Empty future row sets, zero induced counts and empty suffixes have canonical fixed-count spaces; exact law and graph equality handle them without extra positivity assumptions.',
  'No auxiliary Z appears in the natural-history count/collision estimates. It is used only in exact law and disintegration.',
  'Backward direction reverses spatial inequalities only, never chronological tail columns.',
  'Constants are selected before population, horizon, arrays, histories and cylinders. Ambient n in these lemmas is original full population, including in log n.'
 ],
 'quantitative_constants':{'prefix_and_current':'C1=4/reserveMass k D g','tail_collisions':'C2=8/(reserveMass k D g)^2','reserve_denominator':'(reserveMass k D g)^m/2 for m=1 or 2','error':'n*epsilon or n^2*epsilon, charged once per marked tuple'},
 'global_endpoint_scope':'This completes assigned U08 source lemmas. It does not assert C/E/P/T/R or global integration completion.'
}
(audit/'VERIFICATION.json').write_text(json.dumps(verification,indent=2)+'\n')
(audit/'STATUS.txt').write_text(f'''PROVED_AND_CHECKED — U08 assigned source lemmas, both spatial directions.

All {len(sources)} source modules in Reservoir.Module have a fresh successful source build.
Full explicit types, direct dependencies and transitive standard-only axioms checked for {len(rows)} Reservoir declarations, including definitions/private/generated declarations.

PUBLIC RESULTS
historyAtom and historyAtom_backward: exact natural-history multiplicity constraints.
exactMarkedRowLaw: actual sorted-history factorial ratio, residual c+m cancellation and exact prefix marginal.
history_denominator_lower_uniform and backward_history_denominator_lower_uniform: actual H-based denominator >=d0^m/2 for m=1,2.
prefixCount and Backward.prefixCount: C1 n lambda_x^(1-alpha)+n epsilon, C1=4/d0.
extraCurrentCopies and Backward.extraCurrentCopies: excess C_s-t only, same C1, forced observed copies excluded.
tailCollisions and Backward.tailCollisions: C2 n^2 lambda_x^(2(1-alpha)) times the exact suffix power product, plus one n^2 epsilon error, C2=8/d0^2.
conditionalFutureCylinderLaw and conditionalFutureCylinderLaw_unlabeled: actual family-conditioned absolute internal graph has the induced fixed-count graph law, both directions. Matrix and finite expectation versions are also exported.

EVIDENCE
VERIFICATION.json: exact source hashes, commands, receipts, independent U00 reviews and upstream discharge sites.
SOURCE_MAP.json: source equations and proof correspondence.
public-export-types.json: fully explicit public types, dependencies and axioms.
final-declaration-inventory.json: full {len(rows)}-declaration trust/type inventory.
final-fresh-build.log / final-fresh-build-receipt.json: fresh complete Module source build, exit 0.
final-types-and-axioms.log / final-type-axiom-build-receipt.json: full audit, exit 0.

SCOPE
No remaining U08 source proof obligation. Estimates apply at nonempty histories with a last word, exactly as the source. No source conditional law or reserve probability is assumed. Auxiliary Z is confined to conditional averaging; natural-history count estimates retain the frozen history. No independence between distinct cylinders is claimed. U09 owns C assembly and time-zero unconditional F branch. Global endpoint/integration completion is not claimed.
''')
print(json.dumps({'status':'PROVED_AND_CHECKED','declarations':len(rows),'theorems':verification['theorem_count'],'sources':len(sources),'public_exports':len(exports)}))
