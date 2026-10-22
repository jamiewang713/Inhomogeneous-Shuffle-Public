"""Read-only project import graph survey; no compiler or dependency writes."""
from functools import lru_cache
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'before-sources.json').read_text())['modules']
candidates = json.loads((HERE / 'import-candidates.json').read_text())
umbrella = {c['module'] for c in candidates}

@lru_cache(None)
def ancestors(name):
    return {name} | set().union(*(ancestors(dep) for dep in manifest[name]['imports'] if dep in manifest))

result = []
for c in candidates:
    consumers = [n for n in manifest if c['module'] in ancestors(n)]
    unique = [n for n in consumers if ancestors(n) & umbrella == {c['module']}]
    result.append({**c, 'project_consumers_including_self': len(consumers),
                   'sole_umbrella_provider_for': unique,
                   'other_umbrella_ancestors': sorted((ancestors(c['module']) & umbrella) - {c['module']})})
(HERE / 'import-graph-survey.json').write_text(json.dumps(result, indent=2) + '\n')
for r in result:
    print(r['module'], 'consumers:', r['project_consumers_including_self'],
          'sole-provider:', len(r['sole_umbrella_provider_for']),
          'other providers:', ', '.join(r['other_umbrella_ancestors']))
