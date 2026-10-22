"""Compare structural declaration-type fingerprints from two compiled states."""
import json
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
before_label, after_label = sys.argv[1:]
def read(label):
    rows = json.loads((here / f'{label}-declaration-types.json').read_text(encoding='utf-8'))
    result = {r['name']: r for r in rows}
    assert len(rows) == len(result)
    return result
a, b = read(before_label), read(after_label)
shared = a.keys() & b.keys()
changed = {n: {'before': a[n], 'after': b[n]} for n in shared if a[n] != b[n]}
result = {'before_declarations': len(a), 'after_declarations': len(b),
          'unchanged_shared_types': len(shared) - len(changed),
          'changed': changed, 'removed': sorted(a.keys()-b.keys()),
          'added': sorted(b.keys()-a.keys()),
          'method': 'Lean structural Expr hash plus universe parameters and module/name; not a cryptographic proof of equality.'}
(here / 'declaration-type-comparison.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
