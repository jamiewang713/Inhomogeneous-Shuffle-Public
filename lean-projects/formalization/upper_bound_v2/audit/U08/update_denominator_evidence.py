from pathlib import Path
import re,json,hashlib,datetime
p=Path(__file__).resolve().parents[2];a=p/'audit/U08'
v=json.loads((a/'VERIFICATION.json').read_text());names=json.loads((a/'declaration-names.json').read_text());sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
v.update(generated_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PARTIAL',declarations=names,theorem_count=len(names),source_sha256={str(f.relative_to(p)):sha(f) for f in sorted((p/'RiffleUpperV2/Reservoir').glob('*.lean')) if f.name!='ProductUpper.lean'})
v['public_planned_exports']['exactMarkedRowLaw']='PROVED_AND_CHECKED: actual full-pile ratio, residual c+m cancellation, first-column cancellation and actual prefix marginal'
v['quantitative_reserve']='PROVED_AND_CHECKED_FORWARD: history_denominator_lower_uniform, d0^m/2 for m=1,2, actual natural history conditional on exposed base, actual H realization; constants before n,L,cuts/history'
v['build']={'command':'python3 formalization/upper_bound_v2/scripts/build.py --lane U08 --fresh RiffleUpperV2.Reservoir.Module','exit_code':0,'log':'audit/U08/denominator-fresh-build.log','log_sha256':sha(a/'denominator-fresh-build.log'),'receipt':'audit/U08/denominator-fresh-build-receipt.json','scope':'All U08-owned released source fresh; U00 staged immutable dependency source checks; pinned library caches'}
log=(a/'denominator-types-and-axioms.log').read_text();lines=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log);assert len(lines)==len(names),(len(lines),len(names));assert all(all(z.strip() in ('propext','Classical.choice','Quot.sound') for z in re.sub(r'\.\{[^}]*\}', '',vals).split(',')) for _,vals in lines)
v['types_and_axioms']={'command':'python3 formalization/upper_bound_v2/scripts/build.py --lane U08 --run audit/U08/Check.lean','exit_code':0,'log':'audit/U08/denominator-types-and-axioms.log','log_sha256':sha(a/'denominator-types-and-axioms.log'),'receipt':'audit/U08/denominator-type-axiom-build-receipt.json','axioms':['Classical.choice','Quot.sound','propext'],'transitive_checks':len(names),'exact_types':'all implicit parameters exposed with #check @'}
v['remaining_obligations']=['Backward quantitative reserve denominator (backward history atom already proved).','Regular/rare coordinate product bound with alpha and uniform logarithmic error absorption.','Average fixed labeled pile/unmarked-row refinement to the positive natural history, charging H failure once per marked tuple/pair.','Actual prefixCount/extraCurrentCopies/tailCollisions estimates and normalization to lambda_x.','Actual auxiliary Z future-cylinder law under natural sorted history, induced fixed-count internal graph law and disintegration.']
v['upstream_status']={'U07_H':'PROVED_AND_CHECKED; Exploration.UniformConcentration.uniformConcentration','U07_reserve_existence':'PROVED_AND_CHECKED; Exploration.chosenReserves_of_retainedGoodCluster','U07_lexical':'PROVED_AND_CHECKED; fullWord_lt_of_tailPrefix_lt'}
v['independent_review']='U00 source/model/adversarial/build/trust PASS actual uniform forward history denominator: U08-history-denominator-review.json, U08-history-extension-review.json, directional-final-check-build.json; 187 root-audited Reservoir declarations including generated/private.'
(a/'VERIFICATION.json').write_text(json.dumps(v,indent=2)+'\n')
(a/'STATUS.txt').write_text('''PARTIAL — 79 public theorems proved and checked; not lane completion.

RELEASED
Actual forward/backward history atoms and exact marked-row law under the frozen natural history. Exposed factors and first-column factors cancel from the full-pile ratio, leaving exact residual c+m weights. Unused suffix coordinates sum out exactly; actual prefix marginal proved after the concrete unmarked-row prescription and first-column marked condition. Explicit subset enumerations and complement embedding existence are proved.

FORWARD QUANTITATIVE RESERVE
HistoryExtension proves actual chosen right-reserve completions are lexically allowed whenever unmarked rows leave the history satisfied. PilePrefix identifies residual capacities with actual outside-plus-marked counts. Denominator.history_denominator_lower_uniform proves the literal natural-history denominator conditional on the exposed labeled-pile base is >=d0^m/2 for m=1,2, on every base fiber containing an H realization. The threshold is chosen before n,L,cuts,history,pile,marks. No conditional-law or reserve-probability premise is supplied. U07 reserve existence and full H concentration are now checked upstream.

EVIDENCE
Fresh U08 source closure rebuild exit 0: denominator-fresh-build.log and receipt. Exact full types and transitive axioms of all 79 public theorems: denominator-types-and-axioms.log and receipt; only propext, Classical.choice, Quot.sound. Lean 4.33.1 and pinned mathlib; immutable staged upstream dependencies. U00 source/model/adversarial/build/trust review PASS for full current release; 187 Reservoir declarations including generated/private independently audited by root.

REMAINING
Backward quantitative denominator. Regular/rare product control and logarithmic error absorption. Actual positive-natural-history prefix count, removable-copy and collision bounds, with refinement averaging and bad error charged once per tuple/pair. Auxiliary Z future-cylinder law and finite disintegration. ProductUpper.lean is current unexported work in progress, excluded from release source hashes.

No U08 DONE-WHEN or F/C/E/P/T/R endpoint completion is claimed.
''')
print('79 public type/axiom checks verified; evidence updated')
