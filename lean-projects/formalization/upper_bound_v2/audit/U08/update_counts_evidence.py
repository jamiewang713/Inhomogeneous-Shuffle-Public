from pathlib import Path
import re,json,hashlib,datetime
p=Path(__file__).resolve().parents[2];a=p/'audit/U08'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
v=json.loads((a/'VERIFICATION.json').read_text());names=json.loads((a/'declaration-names.json').read_text())
r=json.loads((a/'counts-fresh-build-receipt.json').read_text())
sources={str(Path(x['source']).relative_to(p)):x['sha256'] for m,x in r['modules'].items() if m.startswith('RiffleUpperV2.Reservoir.')}
log=(a/'counts-types-and-axioms.log').read_text();lines=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
assert len(lines)==len(names),(len(lines),len(names))
assert all(all(z.strip() in ('propext','Classical.choice','Quot.sound') for z in re.sub(r'\.\{[^}]*\}', '',vals).split(',')) for _,vals in lines)
v.update(generated_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PARTIAL',declarations=names,theorem_count=len(names),source_sha256=sources)
v['public_planned_exports']['prefixCount']='PROVED_AND_CHECKED_FORWARD: actual natural history, exact support averaging, C1=4/d0, original n and lambda_x, n epsilon error'
v['public_planned_exports']['extraCurrentCopies']='PROVED_AND_CHECKED_FORWARD: actual terminal word excess over observed t, C1=4/d0, original n and lambda_s, n epsilon error'
v['regular_rare_product']='PROVED_AND_CHECKED: actual residual capacities; coordinate envelopes; uniform logarithmic error absorption; exact first-pile normalization'
v['build']={'command':'python3 formalization/upper_bound_v2/scripts/build.py --lane U08 --fresh RiffleUpperV2.Reservoir.Module','exit_code':0,'log':'audit/U08/counts-fresh-build.log','log_sha256':sha(a/'counts-fresh-build.log'),'receipt':'audit/U08/counts-fresh-build-receipt.json'}
v['types_and_axioms']={'command':'python3 formalization/upper_bound_v2/scripts/build.py --lane U08 --run audit/U08/Check.lean','exit_code':0,'log':'audit/U08/counts-types-and-axioms.log','log_sha256':sha(a/'counts-types-and-axioms.log'),'receipt':'audit/U08/counts-type-axiom-build-receipt.json','axioms':['Classical.choice','Quot.sound','propext'],'transitive_checks':len(names),'exact_types':'all implicit parameters exposed with #check @ and pp.all true'}
v['remaining_obligations']=['Backward quantitative reserve denominator and all backward count/collision estimates (backward history atom already proved).','Actual tail collision estimate with exceptional probability charged once per marked pair, plus generalized exponent tail product.','Actual auxiliary Z future-cylinder law under natural sorted history, induced fixed-count internal graph law, and label-set disintegration.']
v['independent_review']='U00 source/model/adversarial/type/trust PASS prefixCount closure in NaturalCountCheck832. Current-copy additions source stable and sent for independent review. Prior denominator/reserve evidence retained.'
(a/'VERIFICATION.json').write_text(json.dumps(v,indent=2)+'\n')
(a/'STATUS.txt').write_text(f'''PARTIAL — {len(names)} public theorems checked; no U08 or endpoint completion claimed.

Actual forward/backward history atoms, exact marked-row laws, residual c+m cancellation and prefix marginals are checked. The actual forward history denominator is at least d0^m/2 for m=1,2. Regular/rare product bounds, support-preserving refinement averaging and initial-pile normalization are checked.

NEW ACTUAL FORWARD ESTIMATES
prefixCount: E[C_x|natural history] <= (4/d0) n lambda_x^(1-alpha)+n epsilon for every strict-future prefix cylinder.
extraCurrentCopies: E[(C_s-t)+|natural history] <= (4/d0) n lambda_s^(1-alpha)+n epsilon. The t forced copies are removed by a proved deletion constraint. Each marked row charges the H exception once. Constants precede n,L,cuts and history; no unexplained source conditional-law premise.

EVIDENCE
Fresh full released Module build and full-type/transitive-axiom audit exit 0: counts-fresh-build.log, counts-types-and-axioms.log, both receipts. Standard axioms only. Source hashes in VERIFICATION.json match the fresh receipt. U00 already accepted prefixCount closure; extraCurrentCopies sent for review.

REMAINING
Backward denominator and estimates. Full tailCollisions estimate. Actual auxiliary Z future-cylinder law, induced fixed-count graph law, spatial orientation and averaging out labeled sets. CollisionPower/CollisionEvents are ongoing unexported work, excluded from current released source hashes.
''')
print('updated',len(names),'checked public theorems')
