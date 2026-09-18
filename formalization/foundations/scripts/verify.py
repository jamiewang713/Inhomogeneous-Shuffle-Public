#!/usr/bin/env python3
"""Check the frozen inventory and export kernel-reported dependency information."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent.parent
expected = '2d48b42c85f7946ddb308efc21d47a4e6b596b497d5c8e447f4ae9ac1062dfd0'
assert hashlib.sha256((root/'CONTRACT.md').read_bytes()).hexdigest() == expected, 'Frozen contract changed'
manifest = json.loads((root/'theorem-manifest.json').read_text())
assert len(manifest) == 74
frozen = dict(re.findall(r'^([PWTMGI]\d\d) `([^`]+)`:', (root/'CONTRACT.md').read_text(), re.M))
assert {x['id']: x['name'].split('.')[-1] for x in manifest} == frozen
actual = []
for source in sorted((root/'RiffleShuffle').glob('*.lean')):
    text = source.read_text()
    code = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(?:axiom|sorry|admit)\b', code), f'Forbidden declaration in {source.name}'
    ns = []
    for line in code.splitlines():
        m = re.match(r'namespace (\w+)', line)
        if m: ns.append(m[1])
        m = re.match(r'end (\w+)', line)
        if m and ns and ns[-1] == m[1]: ns.pop()
        m = re.match(r'(theorem|lemma|instance) ([\w.]+)', line)
        if m and (m[1] != 'instance' or m[2] == 'tree_finite'):
            actual.append('.'.join(ns + [m[2]]))
assert sorted(actual) == sorted(x['name'] for x in manifest), 'Frozen result inventory mismatch'

log = (root/'logs/axioms.log').read_text()
assert 'error:' not in log and 'warning:' not in log
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
checked = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S):
    deps = {a.strip() for a in axioms.split(',') if a.strip()}
    assert deps <= allowed, (name, deps-allowed)
    checked[name] = sorted(deps)
for name in re.findall(r"'([^']+)' does not depend on any axioms", log): checked[name] = []
assert set(checked) == set(actual), 'Missing or extra logical dependency checks'
(root/'axiom-audit.json').write_text(json.dumps(checked, indent=2)+'\n')

kernel = []
for line in (root/'logs/dependencies.log').read_text().splitlines():
    if line.startswith('{'): kernel.append(json.loads(line))
assert kernel, 'No kernel dependency records'
by_name = {x['name']: x['dependencies'] for x in kernel}
visible = set(json.loads((root/'declaration-names.json').read_text()))
assert visible <= by_name.keys()
result = []
for name in sorted(visible):
    project, trusted = set(), set()
    stack = list(by_name[name]); visited = {name}
    while stack:
        dep = stack.pop()
        if dep in visited: continue
        visited.add(dep)
        if not dep.startswith('RiffleShuffle.'):
            trusted.add(dep)
        elif dep in visible:
            project.add(dep)
        else:
            assert dep in by_name, f'Missing generated dependency {dep}'
            stack.extend(by_name[dep])
    result.append({'name':name, 'project_dependencies':sorted(project),
                   'direct_trusted_dependencies':sorted(trusted)})
(root/'kernel-dependencies.json').write_text(json.dumps(kernel, indent=2)+'\n')
(root/'dependencies.json').write_text(json.dumps(result, indent=2)+'\n')
print(f'PASS: {len(actual)} frozen results; unchanged contract; no placeholders or extra axioms.')
print(f'Exported dependencies for {len(visible)} public declarations and {len(kernel)} kernel constants.')
