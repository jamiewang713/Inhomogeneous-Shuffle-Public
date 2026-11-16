#!/usr/bin/env python3
"""Kernel-check the frozen stable-block package and audit every theorem."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent.parent
repo=next(p for p in root.parents if (p/'time_inhomogeneous_riffle_shuffle_unified_article.tex').is_file())
record=json.loads((root/'spec/freeze-record.json').read_text())
for name,digest in record['sha256'].items():
    path=root/'spec/FROZEN_SPEC.md' if name.endswith('/spec/FROZEN_SPEC.md') else repo/name
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    if actual!=digest: raise SystemExit('Frozen input changed: '+name)
modules=['Definitions','Model','Words','Boundary','Mass','Pieces','Cost','Stopping','Retention','SourceStable','Global']
forbidden=re.compile(r'\b(?:axiom|sorry|admit|sorryAx|native_decide)\b')
names=[]; allnames=[]
for m in modules:
    text=(root/f'Riffle/{m}.lean').read_text()
    if forbidden.search(text): raise SystemExit('Forbidden proof escape in '+m)
    for n in re.findall(r'^theorem\s+(\w+)',text,re.M): names.append(('Riffle.'+n,m))
    for n in re.findall(r'^(?:noncomputable\s+)?(?:def|abbrev|structure|inductive|theorem)\s+(\w+)',text,re.M): allnames.append('Riffle.'+n)
(root/'logs').mkdir(exist_ok=True)
with (root/'logs/build.log').open('w') as log:
    for f in [f'Riffle/{m}.lean' for m in modules]+['Riffle.lean']:
        print('Checking '+f,flush=True)
        r=subprocess.run([str(root/'check-file.sh'),f],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log.write(f'FILE {f}\n{r.stdout}\nEXIT {r.returncode}\n');log.flush()
        if r.returncode or 'declaration uses' in r.stdout or 'error:' in r.stdout:
            print(r.stdout);raise SystemExit('Kernel check failed: '+f)
(root/'Audit.lean').write_text('import Riffle\n\n'+''.join('#print axioms '+n+'\n' for n,_ in names))
r=subprocess.run([str(root/'check-file.sh'),'Audit.lean'],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(root/'logs/axioms.log').write_text(r.stdout)
if r.returncode:print(r.stdout);raise SystemExit('Trust audit failed')
allowed={'propext','Classical.choice','Quot.sound'}
entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",r.stdout,re.S)
for name,items in entries:
    found={s.strip() for s in items.split(',') if s.strip()}
    if found-allowed: raise SystemExit('Untrusted dependency: '+name+': '+str(found-allowed))
noaxioms=re.findall(r"'([^']+)' does not depend on any axioms",r.stdout)
if len(entries)+len(noaxioms)!=len(names):raise SystemExit('Incomplete theorem trust inventory')
(root/'theorem-manifest.json').write_text(json.dumps({'theorems':[{'name':n,'module':m} for n,m in names]},indent=2)+'\n')
quoted=',\n    '.join('`'+n for n in allnames)
(root/'Dependencies.lean').write_text('''import Riffle
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names : List Name := [
    '''+quoted+''']
  for name in names do
    let some info := env.find? name | throwError "Missing declaration {name}"
    let deps := info.getUsedConstantsAsSet.toList.filter (fun n => n.toString.startsWith "Riffle.")
    liftIO <| IO.println <| Json.compress <| Json.mkObj
      [("name", toJson name.toString), ("dependencies", toJson (deps.map Name.toString))]
''')
r=subprocess.run([str(root/'check-file.sh'),'Dependencies.lean'],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(root/'logs/dependencies.log').write_text(r.stdout)
if r.returncode:print(r.stdout);raise SystemExit('Dependency audit failed')
deps=[json.loads(line) for line in r.stdout.splitlines() if line.startswith('{')]
if len(deps)!=len(allnames):raise SystemExit('Incomplete declaration dependency inventory')
(root/'kernel-dependencies.json').write_text(json.dumps(deps,indent=2)+'\n')
result={'status':'passed','lean':'4.19.0','mathlib_commit':'c44e0c8ee63ca166450922a373c7409c5d26b00b','modules_checked':len(modules),'theorems_audited':len(names),'declarations_in_dependency_graph':len(deps),'allowed_trusted_logical_axioms':sorted(allowed),'new_project_axioms':0,'proof_placeholders':0,'frozen_input_hashes_verified':True}
(root/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
