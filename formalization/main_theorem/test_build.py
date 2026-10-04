"""Regression tests for build receipt integrity; no Lean process is launched."""
from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import build


class BuildTrustTests(unittest.TestCase):
    VERSION = 'Lean (version 4.33.1, mock compiler, Release)'
    COMPILER = 'mock-lean'

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix='riffle-build-tests-')
        self.addCleanup(temporary.cleanup)
        self.work = Path(temporary.name).resolve() / 'work'
        self.root = self.work / 'formalization' / 'main_theorem'
        self.packages = self.root / '.lake' / 'packages'
        self.lib = self.root / '.build' / 'lean'
        mathlib = self.packages / 'mathlib'
        mathlib.mkdir(parents=True)
        (mathlib / 'lake-manifest.json').write_text('{}', encoding='utf-8')
        self.lock_hook = None
        self.compile_hook = None
        self.compilations: list[Path] = []
        self.output = io.StringIO()
        self.timestamp = 1_600_000_000_000_000_000

        patches = contextlib.ExitStack()
        self.addCleanup(patches.close)
        patches.enter_context(mock.patch.multiple(
            build, ROOT=self.root, WORK=self.work, PACKAGES=self.packages,
            LIB=self.lib, PROJECTS={'RiffleMain': self.root}))
        patches.enter_context(mock.patch.dict(os.environ, {'RIFFLE_LEAN': self.COMPILER}))
        patches.enter_context(mock.patch.object(build, 'module_lock', self.fake_lock))
        patches.enter_context(mock.patch.object(
            build.subprocess, 'check_output', side_effect=self.fake_check_output))
        patches.enter_context(mock.patch.object(
            build.subprocess, 'run', side_effect=self.fake_compile))

    def fake_check_output(self, command, **kwargs):
        if command == [self.COMPILER, '--version']:
            return self.VERSION + '\n'
        if command == ['git', '-C', str(self.packages / 'mathlib'), 'rev-parse', 'HEAD']:
            return build.PIN + '\n'
        self.fail(f'Unexpected external command: {command!r}')

    @contextlib.contextmanager
    def fake_lock(self, name):
        if self.lock_hook is not None:
            self.lock_hook(name)
        yield

    def fake_compile(self, command, **kwargs):
        self.assertEqual(command[0], self.COMPILER)
        self.assertTrue(kwargs.get('check'))
        self.assertEqual(kwargs.get('cwd'), self.root)
        self.assertEqual(kwargs['env']['LEAN_PATH'].split(os.pathsep)[0], str(self.lib))
        source = Path(command[-1])
        target = Path(command[command.index('-o') + 1])
        self.compilations.append(source)
        # Capture the input before a simulated edit during compilation.
        target.write_bytes(b'compiled:' + source.read_bytes())
        if self.compile_hook is not None:
            self.compile_hook(source, target)
        return subprocess.CompletedProcess(command, 0)

    def paths(self, name):
        relative = Path(*name.split('.'))
        source = (self.root / relative).with_suffix('.lean')
        target = (self.lib / relative).with_suffix('.olean')
        return source, target, target.with_suffix('.source.json')

    def cached_module(self, name, text='def cacheValue : Nat := 1\n'):
        source, target, receipt = self.paths(name)
        source.parent.mkdir(parents=True, exist_ok=True)
        target.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(text, encoding='utf-8')
        target.write_bytes(b'compiled:' + source.read_bytes())
        receipt.write_text(json.dumps({
            'sha256': build.sha(source), 'compiler': self.VERSION, 'mathlib': build.PIN,
        }), encoding='utf-8')
        # Distinct fixed timestamps make dependency ordering deterministic.
        self.timestamp += 1_000_000_000
        os.utime(target, ns=(self.timestamp, self.timestamp))
        return source, target, receipt

    def invoke(self, *modules):
        self.output = io.StringIO()
        with mock.patch.object(sys, 'argv', ['build.py', *modules]):
            with contextlib.redirect_stdout(self.output):
                build.main()

    def success_receipts(self):
        return list((self.root / '.build' / 'receipts').glob('*.json'))

    def assert_no_success(self):
        self.assertEqual(self.success_receipts(), [])
        self.assertNotIn('BUILD_OK', self.output.getvalue())

    def test_unchanged_dependency_cache_is_reused(self):
        self.cached_module('RiffleMain.A')
        self.cached_module('RiffleMain.B', 'import RiffleMain.A\ndef b : Nat := 2\n')

        self.invoke('RiffleMain.B')

        self.assertEqual(self.compilations, [])
        self.assertIn('BUILD_OK RiffleMain.B', self.output.getvalue())
        records = self.success_receipts()
        self.assertEqual(len(records), 1)
        manifest = json.loads(records[0].read_text(encoding='utf-8'))
        self.assertEqual(manifest['status'], 'BUILD_OK')
        self.assertEqual(set(manifest['modules']), {'RiffleMain.A', 'RiffleMain.B'})

    def test_source_restored_during_rebuild_cannot_reuse_old_receipt(self):
        original = 'def cacheValue : Nat := 1\n'
        changed = 'def cacheValue : Nat := 2\n'
        source, target, receipt = self.cached_module('RiffleMain.A', original)
        original_bytes = source.read_bytes()
        source.write_text(changed, encoding='utf-8')
        changed_bytes = source.read_bytes()

        def restore_source(compiled_source, compiled_target):
            self.assertEqual(compiled_source, source)
            self.assertFalse(receipt.exists(), 'Old success receipt must be invalidated first')
            source.write_text(original, encoding='utf-8')

        self.compile_hook = restore_source
        with self.assertRaisesRegex(RuntimeError, 'Source changed during compilation'):
            self.invoke('RiffleMain.A')

        self.assertEqual(target.read_bytes(), b'compiled:' + changed_bytes)
        self.assertFalse(receipt.exists())
        self.assert_no_success()

        # Even though the source again equals the old receipt's source, the
        # next run must compile it instead of accepting the mismatched object.
        self.compile_hook = None
        self.invoke('RiffleMain.A')
        self.assertEqual(self.compilations, [source, source])
        self.assertEqual(target.read_bytes(), b'compiled:' + original_bytes)
        self.assertEqual(json.loads(receipt.read_text())['sha256'], build.sha(source))

    def test_source_change_while_waiting_rejects_cache_hit(self):
        source, _, _ = self.cached_module('RiffleMain.A')

        def edit_at_lock(name):
            self.assertEqual(name, 'RiffleMain.A')
            source.write_text('def cacheValue : Nat := 2\n', encoding='utf-8')

        self.lock_hook = edit_at_lock
        with self.assertRaisesRegex(RuntimeError, 'Source changed while waiting'):
            self.invoke('RiffleMain.A')

        self.assertEqual(self.compilations, [])
        self.assert_no_success()

    def test_late_change_to_visited_dependency_blocks_overall_success(self):
        source, _, _ = self.cached_module('RiffleMain.A')
        self.cached_module('RiffleMain.B', 'import RiffleMain.A\ndef b : Nat := 2\n')

        def edit_earlier_source(name):
            if name == 'RiffleMain.B':
                source.write_text('def cacheValue : Nat := 2\n', encoding='utf-8')

        self.lock_hook = edit_earlier_source
        with self.assertRaisesRegex(RuntimeError, 'Source changed before final verification'):
            self.invoke('RiffleMain.A', 'RiffleMain.B')

        self.assertEqual(self.compilations, [])
        self.assert_no_success()

    def test_compiler_failure_invalidates_old_success_receipt(self):
        source, _, receipt = self.cached_module('RiffleMain.A')
        source.write_text('def cacheValue : Nat := 2\n', encoding='utf-8')

        def fail_compilation(compiled_source, compiled_target):
            raise subprocess.CalledProcessError(1, [self.COMPILER])

        self.compile_hook = fail_compilation
        with self.assertRaises(subprocess.CalledProcessError):
            self.invoke('RiffleMain.A')

        self.assertFalse(receipt.exists())
        self.assert_no_success()

    def test_receipt_compiler_and_mathlib_must_match(self):
        source, _, receipt = self.cached_module('RiffleMain.A')
        for key, invalid in [('compiler', 'other compiler'), ('mathlib', 'other revision')]:
            with self.subTest(key=key):
                record = json.loads(receipt.read_text())
                record[key] = invalid
                receipt.write_text(json.dumps(record), encoding='utf-8')
                before = len(self.compilations)

                self.invoke('RiffleMain.A')

                self.assertEqual(len(self.compilations), before + 1)
                self.assertEqual(self.compilations[-1], source)
                expected = self.VERSION if key == 'compiler' else build.PIN
                self.assertEqual(json.loads(receipt.read_text())[key], expected)

    def test_late_receipt_change_blocks_overall_success(self):
        _, _, receipt = self.cached_module('RiffleMain.A')
        self.cached_module('RiffleMain.B', 'import RiffleMain.A\ndef b : Nat := 2\n')

        def change_earlier_receipt(name):
            if name == 'RiffleMain.B':
                record = json.loads(receipt.read_text())
                record['mathlib'] = 'other revision'
                receipt.write_text(json.dumps(record), encoding='utf-8')

        self.lock_hook = change_earlier_receipt
        with self.assertRaisesRegex(RuntimeError, 'Compilation receipt changed before final verification'):
            self.invoke('RiffleMain.A', 'RiffleMain.B')

        self.assertEqual(self.compilations, [])
        self.assert_no_success()


if __name__ == '__main__':
    unittest.main()
