#!/usr/bin/env python3
"""Read-only verification of additive dependency receipts; preserves the v1 tools."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        sys.exit(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('receipt', help='Directory name under Contracts/dependencies')
    parser.add_argument('--sources-only', action='store_true',
                        help='Skip local output fingerprints before a coordinator rebuild')
    args = parser.parse_args()
    require(Path(args.receipt).name == args.receipt, 'Expected a receipt directory name')
    directory = ROOT / 'Contracts/dependencies' / args.receipt
    for rel, digest in json.loads((directory / 'SHA256.json').read_text()).items():
        require(sha(ROOT / rel) == digest, 'Additive receipt file changed: ' + rel)
    data = json.loads((directory / 'SOURCES.json').read_text())
    frozen = ROOT / 'Contracts/v1/SHA256.json'
    require(sha(frozen) == data['base_manifest_sha256'], 'Base manifest changed')
    for rel, digest in json.loads(frozen.read_text()).items():
        require(sha(ROOT / rel) == digest, 'Frozen v1 file changed: ' + rel)
    spec = importlib.util.spec_from_file_location('foundation_build', ROOT / 'build.py')
    build = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(build)
    release = json.loads((ROOT / 'Contracts/v1/SOURCES.json').read_text())
    for rel, digest in release['external_files'].items():
        require(sha(build.WORK / rel) == digest, 'Original external source changed: ' + rel)
    require(sha(build.COMPILER) == data['compiler_sha256'], 'Compiler fingerprint changed')
    version = subprocess.check_output([str(build.COMPILER), '--version'], text=True).strip()
    require(version == data['compiler'], 'Compiler version changed')
    for package, revision in data['dependency_revisions'].items():
        actual = subprocess.check_output(
            ['git', '-C', str(build.PACKAGES / package), 'rev-parse', 'HEAD'], text=True).strip()
        require(actual == revision, 'Dependency revision changed: ' + package)
    for name, entry in data['modules'].items():
        if entry['kind'] == 'pinned-library':
            path = build.PACKAGES / entry['package'] / entry['package_relative_source']
        else:
            path = build.WORK / entry['workspace_relative_source']
        require(sha(path) == entry['sha256'], 'Registered source changed: ' + name)
    if not args.sources_only:
        for rel, digest in data['new_output_sha256'].items():
            require(sha(ROOT / rel) == digest, 'Registered dependency output changed: ' + rel)
    suffix = 'SOURCES_OK' if args.sources_only else 'DEPENDENCIES_OK'
    print(args.receipt + ' ' + suffix)


if __name__ == '__main__':
    main()
