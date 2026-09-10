"""Non-compiler regression tests for the narrow, append-only R193 retry gate."""
import hashlib
import json
from pathlib import Path
import runpy
import tempfile
import tarfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
OUT = Path('/tmp/dgamma-r193')
AUTH = runpy.run_path(str(ROOT/'research-tests/r193_validation_continuation.py'))


def evidence_bytes(name):
    if (OUT/name).is_file():
        return (OUT/name).read_bytes()
    with tarfile.open(ROOT/'research-tests/O6-R193-COMPILER-EVIDENCE.tar.gz', 'r:gz') as archive:
        return archive.extractfile('dgamma-r193/'+name).read()


class ContinuationGateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)/'root'
        self.out = Path(self.tmp.name)/'out'
        (self.root/'research-tests').mkdir(parents=True)
        self.out.mkdir()
        for name in ['final-validation-plan.json', 'final-validation-plan.sha256',
                     'final-validation-continuation.json', 'final-validation-continuation.sha256',
                     'V1.json', 'V2.json']:
            (self.out/name).write_bytes(evidence_bytes(name))
        for name in ['O6-R193-FINAL-VALIDATION-PLAN.json', 'O6-R193-FINAL-VALIDATION-CONTINUATION.json']:
            (self.root/'research-tests'/name).write_bytes((ROOT/'research-tests'/name).read_bytes())
        self.manifest = json.loads((self.out/'final-validation-continuation.json').read_text())
        self.source = (ROOT/self.manifest['retry']['path']).read_bytes()
        self.target = self.root/self.manifest['retry']['path']
        self.target.parent.mkdir(parents=True)
        self.target.write_bytes(self.source)
        mock = patch.object(AUTH['subprocess'], 'check_output', return_value=self.source)
        self.git = mock.start()
        self.addCleanup(mock.stop)

    def authenticate(self):
        return AUTH['authenticate'](self.root, self.out)

    def rewrite_manifest(self):
        raw = (json.dumps(self.manifest, indent=2)+'\n').encode()
        (self.out/'final-validation-continuation.json').write_bytes(raw)
        (self.root/'research-tests/O6-R193-FINAL-VALIDATION-CONTINUATION.json').write_bytes(raw)
        (self.out/'final-validation-continuation.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')

    def test_exact_authorized_continuation(self):
        manifest, plan = self.authenticate()
        self.assertEqual(len(plan), 52)
        self.assertEqual([x['unit'] for x in plan[:3]], ['V1', 'V2R1', 'V3'])
        self.assertEqual(manifest['retryRSSLimitKiB'], 54525952)
        self.git.assert_called_once_with(['git', 'show', '77a9efe1:'+manifest['retry']['path']], cwd=self.root)

    def test_changed_local_diamond_is_rejected(self):
        self.target.write_bytes(self.source+b'\n-- changed\n')
        with self.assertRaises(AssertionError):
            self.authenticate()

    def test_other_check_guard_cannot_be_raised(self):
        self.manifest['defaultRSSLimitKiB'] = 52*1024*1024
        self.rewrite_manifest()
        with self.assertRaises(AssertionError):
            self.authenticate()

    def test_retry_guard_cannot_exceed_52_gib(self):
        self.manifest['retryRSSLimitKiB'] = 53*1024*1024
        self.rewrite_manifest()
        with self.assertRaises(AssertionError):
            self.authenticate()

    def test_no_third_attempt(self):
        self.manifest['maximumRetryCount'] = 2
        self.rewrite_manifest()
        with self.assertRaises(AssertionError):
            self.authenticate()

    def test_no_additional_substitution(self):
        self.manifest['substitutions']['V3'] = 'V3R1'
        self.rewrite_manifest()
        with self.assertRaises(AssertionError):
            self.authenticate()

    def test_original_failure_cannot_be_relabelled(self):
        old = json.loads((self.out/'V2.json').read_text())
        old['passed'] = True
        (self.out/'V2.json').write_text(json.dumps(old))
        with self.assertRaises(AssertionError):
            self.authenticate()

    def test_original_plan_cannot_be_overwritten(self):
        raw = (self.out/'final-validation-plan.json').read_bytes()+b'\n'
        (self.out/'final-validation-plan.json').write_bytes(raw)
        (self.root/'research-tests/O6-R193-FINAL-VALIDATION-PLAN.json').write_bytes(raw)
        (self.out/'final-validation-plan.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
        with self.assertRaises(AssertionError):
            self.authenticate()


if __name__ == '__main__':
    unittest.main()
