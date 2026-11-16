"""Check active source placeholders, diagnostic commands, and heartbeat invariance."""
import json
from pathlib import Path
import re
import sys

from layout import EVIDENCE as HERE, PROJECTS
before = json.loads((HERE / 'before-sources.json').read_text())
label = sys.argv[1] if len(sys.argv) > 1 else 'after2'
after = json.loads((HERE / f'{label}-sources.json').read_text())
assert before['modules'].keys() == after['modules'].keys()

def inspect(root, manifest):
    result = {'placeholders': [], 'diagnostic_commands': [], 'heartbeat_settings': []}
    for module, info in manifest['modules'].items():
        text = (root / info['path']).read_text(encoding='utf-8')
        for i, line in enumerate(text.splitlines(), 1):
            if re.search(r'\b(sorry|admit|sorryAx)\b', line):
                result['placeholders'].append([module, i, line.strip()])
            if re.match(r'\s*#(?:check|print|eval|reduce|exit)\b', line):
                result['diagnostic_commands'].append([module, i, line.strip()])
            if re.search(r'\bset_option\s+\S*[Hh]eartbeats\b', line):
                result['heartbeat_settings'].append([module, line.strip()])
    return result

a = inspect(Path(before['snapshot_path']), before)
b = inspect(PROJECTS, after)
assert not a['placeholders'] and not b['placeholders'], 'Inspect possible placeholder tokens'
assert not a['diagnostic_commands'] and not b['diagnostic_commands']
assert a['heartbeat_settings'] == b['heartbeat_settings']
result = {'modules_checked': len(after['modules']), 'before': a, 'after': b,
          'heartbeat_settings_unchanged': True,
          'method': 'Conservative raw-source token scan; any match requires review, even in comments.'}
(HERE / 'active-source-audit.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print('ACTIVE_SOURCE_AUDIT_OK:', len(after['modules']), 'modules;',
      len(b['heartbeat_settings']), 'unchanged heartbeat settings')
