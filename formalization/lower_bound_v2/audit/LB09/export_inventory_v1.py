"""Summarize the checked LB09 environment without modifying shared release files."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'audit/LB09'
log=(OUT/'compiled-audit-v2.log').read_text()
assert 'LB09_REQUIRED_THEOREMS_VERIFIED' in log
assert 'error:' not in log and 'error(' not in log
rows={}
for line in log.splitlines():
    if line.startswith('DECLARATION_JSON '):
        row=json.loads(line[len('DECLARATION_JSON '):]); rows[row['name']]=row
allowed={'propext','Classical.choice','Quot.sound'}
assert rows and all(set(r['axioms'])<=allowed and r['kind']!='axiom' for r in rows.values())
targets={'relativeEndpoint':'RelativeEndpointTarget',
 'deterministicColdGeometry':'DeterministicColdGeometryTarget',
 'localization':'LocalizationTarget',
 'coldGeometryFromEmpirical':'ColdGeometryFromEmpiricalTarget',
 'lB09':'LB09Target'}
required={}
for name,typ in targets.items():
    row=rows['RiffleLowerV2.Localization.'+name]
    assert row['kind']=='theorem' and row['type']=='RiffleLowerV2.Targets.'+typ
    required[row['name']]=row['type']
public={};sources={}
for p in sorted((ROOT/'RiffleLowerV2/Localization').rglob('*.lean')):
    body=p.read_text(); rel=str(p.relative_to(ROOT))
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',body),rel
    sources[rel]=hashlib.sha256(p.read_bytes()).hexdigest()
    for line_no,line in enumerate(body.splitlines(),1):
        match=re.match(r'^(?:@\[[^\n]*\]\s*)?(theorem|lemma|def)\s+([^\s({]+)',line)
        if not match:continue
        name='RiffleLowerV2.Localization.'+match[2]
        assert name in rows,(rel,line_no,name)
        public[name]={**rows[name],'source':rel,'line':line_no}
lines=['# LB09 exact checked exports v1','','All five required exports are proved theorems of their unchanged frozen target types. The types below are printed from the compiled Lean environment. Target definitions are not counted as proofs.','']
for name,row in sorted(public.items()):
    lines += ['## '+name,'','Source: `'+row['source']+':'+str(row['line'])+'`. Kind: '+row['kind']+'.','','```lean',name+' : '+row['type'],'```','','Transitive axioms: '+(', '.join('`'+a+'`' for a in sorted(row['axioms'])) or 'none')+'.','']
summary={'status':'LB09_PROVED','required_exports':required,'compiled_declarations':len(rows),'public_exports':len(public),'public_theorems':sum(r['kind']=='theorem' for r in public.values()),'axiom_union':sorted(set(a for r in rows.values() for a in r['axioms'])),'source_sha256':sources,'frozen_target_changed':False,'pending_LB09_proof_obligations':[]}
for name,data in [('compiled-declarations-v1.json',rows),('public-exports-v1.json',public),('verification-v1.json',summary),('SOURCES_v1.json',sources)]:
    with (OUT/name).open('x') as f:json.dump(data,f,indent=2,ensure_ascii=False);f.write('\n')
with (OUT/'EXPORTS_v1.md').open('x') as f:f.write('\n'.join(lines))
print(json.dumps({k:v for k,v in summary.items() if k!='source_sha256'},indent=2))
