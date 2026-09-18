#!/usr/bin/env python3
"""Compile missing pinned library modules into a local overlay, without editing the cache."""
from pathlib import Path
import os
import re
import subprocess

import build

ROOT = Path(__file__).resolve().parent
REQUIRED = ['Mathlib.Probability.Distributions.Uniform',
            'Mathlib.Probability.ProbabilityMassFunction.Integrals']


def main():
    packages = Path(os.environ.get('RIFFLE_PACKAGES', str(build.DEFAULT_PACKAGES)))
    compiler = Path(os.environ.get('RIFFLE_LEAN', str(build.DEFAULT_TOOLS / 'bin/lean')))
    output = ROOT / '.build'
    libraries = [output] + [p / '.lake/build/lib/lean' for p in sorted(packages.iterdir())
                           if (p / '.lake/build/lib/lean').is_dir()]
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, libraries))
    pending, order = {}, []

    def visit(name):
        relative = Path(name.replace('.', '/'))
        if name in pending or any((p / relative.with_suffix('.olean')).is_file()
                                  for p in libraries):
            return
        source = next((p / relative.with_suffix('.lean') for p in packages.iterdir()
                       if (p / relative.with_suffix('.lean')).is_file()), None)
        if source is None:
            raise SystemExit(f'Missing library source: {name}')
        pending[name] = source
        for line in source.read_text().splitlines():
            match = re.match(r'^(?:public |private )?import (.+)', line)
            if match:
                for dependency in match.group(1).split():
                    if dependency.startswith('--'):
                        break
                    visit(dependency)
        order.append(name)

    for name in REQUIRED:
        visit(name)
    # Lean resolves a top-level namespace in one search-path root. Supply a
    # complete read-only view, expanding only paths where a new file is built.
    overrides = {Path(name.replace('.', '/')) for name in REQUIRED + order}

    def overlay_directory(source, target, relative):
        if target.is_symlink():
            target.unlink()
        target.mkdir(parents=True, exist_ok=True)
        if not source.is_dir():
            return
        for entry in source.iterdir():
            rel = relative / entry.name
            dest = target / entry.name
            if entry.is_dir() and any(rel == p or rel in p.parents for p in overrides):
                overlay_directory(entry, dest, rel)
            elif any(rel.parent == p.parent and entry.name.startswith(p.name + '.')
                     for p in overrides):
                if dest.is_symlink():
                    dest.unlink()
            elif not dest.exists() and not dest.is_symlink():
                dest.symlink_to(entry, target_is_directory=entry.is_dir())

    for top_name in sorted({p.parts[0] for p in overrides}):
        cached = next((p / top_name for p in libraries[1:] if (p / top_name).is_dir()), None)
        if cached is not None:
            overlay_directory(cached, output / top_name, Path(top_name))
    for name in order:
        source = pending[name]
        relative = Path(name.replace('.', '/')).with_suffix('.olean')
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        package_root = source
        for _ in name.split('.'):
            package_root = package_root.parent
        print(f'Checking pinned library source {name}', flush=True)
        subprocess.run([str(compiler), '-R', str(package_root), '-o', str(target),
                        str(source)], cwd=ROOT, env=env, check=True)
    print('Required pinned library modules are available.', flush=True)


if __name__ == '__main__':
    main()
