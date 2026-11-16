#!/usr/bin/env python3
"""Summarize Lean's checked declarations; refuses missing source exports or illicit axioms."""
from pathlib import Path
import argparse,json,re
ROOT=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--log',default='.build/new-audit.log');ap.add_argument('--out',default='.build/new-audit');ap.add_argument('--exports');args=ap.parse_args()
AUDIT=(ROOT/args.out).resolve();log=(ROOT/args.log).resolve()
frozen=(ROOT/'Contracts/v1/SHA256.json').exists()
if frozen and (ROOT/'audit').resolve() in AUDIT.parents:raise SystemExit('Released audit snapshots must not be overwritten; use .build/')
AUDIT.mkdir(parents=True,exist_ok=True)
raw={}
for line in log.read_text().splitlines():
    if 'DECLARATION_JSON ' in line:
        row=json.loads(line.split('DECLARATION_JSON ',1)[1]);raw[row['name']]=row
if not raw or not log.read_text().rstrip().endswith('BUILD_OK'):
    raise SystemExit('No successful compiled audit')
allowed={'propext','Classical.choice','Quot.sound'}
for name,row in raw.items():
    if set(row['axioms'])-allowed:raise SystemExit('Forbidden axiom at '+name)
    if row['kind']=='axiom':raise SystemExit('Project axiom '+name)
public={}
for folder in ('RiffleLowerV2','Contracts'):
    for p in sorted((ROOT/folder).rglob('*.lean')):
        namespace='RiffleLowerV2.Targets' if 'namespace RiffleLowerV2.Targets' in p.read_text() else 'RiffleLowerV2'
        for number,line in enumerate(p.read_text().splitlines(),1):
            m=re.match(r'^(?:@\[[^\n]*\]\s*)?(theorem|lemma|def|abbrev|structure)\s+([^\s({]+)',line)
            if not m:continue
            kind,local=m.groups();name=namespace+'.'+local
            if name not in raw:raise SystemExit('Public source declaration absent from compiled environment: '+name)
            public[name]={**raw[name], 'source':str(p.relative_to(ROOT)),'line':number,'source_kind':kind}
(AUDIT/'compiled-declarations.json').write_text(json.dumps(raw,indent=2,ensure_ascii=False)+'\n')
(AUDIT/'public-exports.json').write_text(json.dumps(public,indent=2,ensure_ascii=False)+'\n')
lines=['# Exact compiled exports — LB-00 v1','','Generated from the compiled Lean environment. **A definition of a proposition is only a checked statement, not a proof.** Every downstream target below remains pending. Theorems listed here are routine shared foundation adapters only.','']
for name,item in sorted(public.items()):
    status='PROVED shared adapter' if item['kind']=='theorem' else ('PENDING target; statement checked' if item['type']=='Prop' else 'DEFINED and type checked')
    lines += ['## '+name,'',status+'. Source: `'+item['source']+':'+str(item['line'])+'`.','', '```lean', name+' : '+item['type']]
    if item['type']=='Prop':lines += ['-- Target statement:',item['value']]
    lines += ['```','', 'Axiom closure: '+(', '.join('`'+a+'`' for a in sorted(item['axioms'])) or 'none')+'.','']
export_text='\n'.join(lines)
expected=ROOT/'Contracts/v1/EXPORTS.md'
if frozen and expected.read_text()!=export_text:raise SystemExit('Compiled exports differ from immutable release')
dest=(ROOT/args.exports).resolve() if args.exports else AUDIT/'EXPORTS.md'
if frozen and dest==expected.resolve():raise SystemExit('Do not overwrite the released export inventory')
dest.write_text(export_text)
summary={'declarations_audited':len(raw),'public_exports':len(public),'proved_public_adapters':[n for n,x in public.items() if x['kind']=='theorem'], 'pending_typed_targets':[n for n,x in public.items() if x['type']=='Prop'], 'axiom_union':sorted(set(a for x in raw.values() for a in x['axioms'])), 'source_targets_are_proved':False}
(AUDIT/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:(len(v) if isinstance(v,list) and k!='axiom_union' else v) for k,v in summary.items()},indent=2))
