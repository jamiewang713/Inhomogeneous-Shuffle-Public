"""Run an audit/probe outside the measured library roots, without emitting oleans."""
import sys
import measure as m

label, filename, *extra = sys.argv[1:]
_, env = m.preflight()
env['RIFFLE_TYPE_DUMP'] = str(m.HERE / f'{label}-declaration-types.json')
source = m.HERE / filename
base = m.REPO if source.is_relative_to(m.REPO) else source.parent
logfile = m.HERE / f'{label}-{source.stem}.log'
with logfile.open('wb') as log:
    stats = m.measured([m.COMPILER, '-j1', *extra, '-R', base, source], log,
                       cwd=m.ROOT, env=env)
m.write_json(logfile.with_suffix('.json'), stats)
print(logfile.read_text(encoding='utf-8', errors='replace'))
print('Exit:', stats['exit_code'], 'CPU:', stats['user_s'] + stats['system_s'])
raise SystemExit(stats['exit_code'])
