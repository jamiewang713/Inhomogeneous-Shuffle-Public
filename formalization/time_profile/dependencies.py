#!/usr/bin/env python3
"""Extract project dependency edges from compiled Lean expressions."""
from pathlib import Path
import json
import os
import re
import subprocess

import build

ROOT = Path(__file__).resolve().parent


def main():
    output = ROOT / '.build'
    script = output / 'DependencyAudit.lean'
    script.write_text('''import RiffleTimeProfile
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let text := name.toString
    if text.startsWith "TimeProfile." || text.startsWith "_private.RiffleTimeProfile." then
      let typeNames := info.type.getUsedConstants.map Name.toString
      let valueNames := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants.map Name.toString
        | none => #[]
      let data := Json.mkObj [("name", toJson text),
        ("type", toJson typeNames), ("value", toJson valueNames)]
      logInfo m!"DEPENDENCY_JSON {data.compress}"
''')
    packages = Path(os.environ.get('RIFFLE_PACKAGES', str(build.DEFAULT_PACKAGES)))
    compiler = Path(os.environ.get('RIFFLE_LEAN', str(build.DEFAULT_TOOLS / 'bin/lean')))
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(output)] + [
        str(p / '.lake/build/lib/lean') for p in sorted(packages.iterdir())
        if (p / '.lake/build/lib/lean').is_dir()])
    result = subprocess.run([str(compiler), str(script)], cwd=ROOT, env=env,
                            capture_output=True, text=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    raw = {}
    for line in result.stdout.splitlines():
        if 'DEPENDENCY_JSON ' in line:
            item = json.loads(line.split('DEPENDENCY_JSON ', 1)[1])
            raw[item['name']] = item
    public = {}
    for module in build.ORDER:
        source = ROOT / 'RiffleTimeProfile' / f'{module}.lean'
        for lineno, line in enumerate(source.read_text().splitlines(), 1):
            match = re.match(r'^(?:@\[[^\n]*\]\s*)?(?:protected\s+)?'
                             r'(theorem|lemma|def|abbrev|structure)\s+([^\s({]+)', line)
            if match:
                kind, local = match.groups()
                name = 'TimeProfile.' + local
                if name not in raw:
                    raise SystemExit(f'Missing compiled declaration: {name}')
                public[name] = {'module': module, 'line': lineno, 'kind': kind}

    def collapse(names, self_name):
        result, seen, queue = set(), set(), list(names)
        while queue:
            name = queue.pop()
            if name in seen or name == self_name:
                continue
            seen.add(name)
            if name in public:
                result.add(name)
            elif name in raw:
                queue.extend(raw[name]['type'])
                queue.extend(raw[name]['value'])
        return sorted(result)

    ledger = {}
    for name, meta in public.items():
        entry = raw[name]
        ledger[name] = {**meta,
            'statement_dependencies': collapse(entry['type'], name),
            'proof_or_definition_dependencies': collapse(entry['value'], name),
            'direct_external_constants': sorted(set(entry['type'] + entry['value']) - set(raw))}
    (ROOT / 'dependencies.json').write_text(json.dumps(ledger, indent=2) + '\n')
    lines = ['# Compiled declaration dependencies', '',
             'Generated from the types and bodies accepted by Lean. The table covers every '
             'public project definition, structure and theorem. Private helpers and generated '
             'project declarations are expanded until reaching public project declarations. '
             'Trusted external constants are recorded separately in `dependencies.json`. '
             'The source-level upper/lower/random-pile architecture and F/P/A/M classification '
             'remain in `PROOF_MAP.md`.', '',
             '| Declaration | Kind | Statement dependencies | Proof or definition dependencies |',
             '|---|---|---|---|']
    def label(name):
        item = public[name]
        short = name.removeprefix('TimeProfile.')
        return f'[{short}](RiffleTimeProfile/{item["module"]}.lean#L{item["line"]})'
    for name, item in ledger.items():
        types = ', '.join(label(dep) for dep in item['statement_dependencies']) or '—'
        values = ', '.join(label(dep) for dep in item['proof_or_definition_dependencies']) or '—'
        lines.append(f'| {label(name)} | {item["kind"]} | {types} | {values} |')
    (ROOT / 'DEPENDENCIES.md').write_text('\n'.join(lines) + '\n')
    print(f'Extracted compiled dependencies for {len(public)} public declarations.')


if __name__ == '__main__':
    main()
