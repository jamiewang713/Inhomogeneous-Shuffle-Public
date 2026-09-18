#!/usr/bin/env python3
"""Extract direct dependencies from elaborated Lean types and proof terms."""
from pathlib import Path
import json
import re
import subprocess

root = Path(__file__).resolve().parent
entries = []
for path in sorted((root / 'RiffleLower').glob('*.lean')):
    source = path.read_text()
    pattern = r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|def|abbrev|structure)\s+(\w+)'
    for match in re.finditer(pattern, source, re.M):
        entries.append(dict(name='RiffleLower.' + match.group(2), kind=match.group(1),
                            source=str(path.relative_to(root)),
                            line=source.count('\n', 0, match.start()) + 1))

lean = '''import RiffleLower
import Lean.Util.FoldConsts
open Lean in
run_cmd do
  let env ← getEnv
  let names : Array Name := #[%s]
  for name in names do
    let some info := env.find? name | throwError "Missing declaration {name}"
    let values := match info.value? with
      | some value => value.getUsedConstants
      | none => #[]
    let constants := (info.type.getUsedConstants ++ values).toList
    logInfo ("DEPENDENCY|" ++ name.toString ++ "|" ++
      String.intercalate "," (constants.map Name.toString))
''' % ', '.join('`' + entry['name'] for entry in entries)
audit = root / '.lake/DependencyAudit.lean'
audit.write_text(lean)
result = subprocess.run([str(root / 'run_lean.sh'), '.lake/DependencyAudit.lean'],
                        cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
if result.returncode:
    raise SystemExit(result.stdout)
observed = dict(re.findall(r'DEPENDENCY\|([^|\n]+)\|([^\n]*)', result.stdout))
for entry in entries:
    if entry['name'] not in observed:
        raise SystemExit('Missing dependency output for ' + entry['name'])
    names = sorted(set(observed[entry['name']].split(',')) - {entry['name'], ''})
    entry['project_dependencies'] = [n for n in names if n.startswith('RiffleLower.')]
    entry['trusted_dependencies'] = [n for n in names if not n.startswith('RiffleLower.')]
(root / 'audit/lean-dependencies.json').write_text(json.dumps(entries, indent=2) + '\n')
lines = ['# Elaborated Lean dependency graph', '',
         'These direct edges are extracted from Lean declaration types and proof terms,',
         'not inferred from source text. The JSON also records trusted-library dependencies.', '',
         '| Declaration | Kind | Direct project dependencies |', '|---|---|---|']
for entry in entries:
    deps = ', '.join('`' + n.removeprefix('RiffleLower.') + '`' for n in entry['project_dependencies'])
    lines.append(f"| `{entry['name'].removeprefix('RiffleLower.')}` | {entry['kind']} | {deps or 'Trusted Lean/mathlib only'} |")
(root / 'audit/lean-dependencies.md').write_text('\n'.join(lines) + '\n')
print(f'Extracted exact direct dependencies for {len(entries)} declarations.')
