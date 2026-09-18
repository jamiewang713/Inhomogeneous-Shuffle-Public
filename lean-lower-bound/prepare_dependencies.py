#!/usr/bin/env python3
"""Compile missing trusted-library modules into this project's cache only."""
from pathlib import Path
import os,re,subprocess,sys
root=Path(__file__).resolve().parent
mathlib=Path(os.environ.get('RIFFLE_MATHLIB',root.parent/'formalization/.tooling/mathlib')).resolve()
toolchain=Path(os.environ.get('RIFFLE_TOOLCHAIN',root.parent/'formalization/.tooling/lean-4.19.0-darwin_aarch64')).resolve()
packages=list((mathlib/'.lake/packages').iterdir())
overlay=root/'.lake/dependency-cache'
overlay.mkdir(parents=True,exist_ok=True)
# Lean resolves a module's root namespace from one search-path entry. Mirror the
# existing cache with file symlinks so locally compiled missing modules and the
# trusted prebuilt modules coexist without modifying another project.
for cached in (mathlib/'.lake/build/lib/lean').rglob('*'):
    if cached.is_file():
        target=overlay/cached.relative_to(mathlib/'.lake/build/lib/lean')
        target.parent.mkdir(parents=True,exist_ok=True)
        if not target.exists(): target.symlink_to(cached)
paths=[root/'.lake/build/lib/lean',overlay,mathlib/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in packages]+[toolchain/'lib/lean']
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)))
seen=set()
def ensure(mod):
    if mod in seen: return
    seen.add(mod)
    rel=Path(*mod.split('.'))
    if any((p/rel.with_suffix('.olean')).exists() for p in paths): return
    source=None
    for base in [mathlib]+packages:
        candidate=base/rel.with_suffix('.lean')
        if candidate.exists(): source=candidate; source_root=base; break
    if source is None: raise RuntimeError('No trusted source for '+mod)
    for line in source.read_text().splitlines():
        hit=re.match(r'^(?:public )?import\s+(.+?)(?:\s*--.*)?$',line)
        if hit:
            for dep in hit.group(1).split(): ensure(dep)
    out=overlay/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
    print('Checking trusted dependency',mod,flush=True)
    subprocess.run([str(toolchain/'bin/lean'),'--root='+str(source_root),'-o',str(out),str(source)],cwd=root,env=env,check=True)
for module in sys.argv[1:]: ensure(module)
