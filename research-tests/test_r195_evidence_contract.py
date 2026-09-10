"""Noncompiler regressions: no Idris invocation or source/cache mutation."""
import hashlib
import importlib.util
import pathlib
import unittest

HERE = pathlib.Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('contract', HERE / 'r195_evidence_contract.py')
contract = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(contract)

class EvidenceContractTests(unittest.TestCase):
    def sample(self):
        source = b'module DGamma.Example\n'
        log = '1/1: Building DGamma.Example (research/DGamma/Example.idr)\n'
        record = dict(unit='A1-1', path='research/DGamma/Example.idr', sourceSHA256=hashlib.sha256(source).hexdigest(),
                      transcript=log, passed=True, fresh=True, interrupted=False, targetMutationDetected=False,
                      rssSamples=[dict(rssKiB=42)], maxSampleRSSKiB=42, expectedDiagnostic=None, symbol=None, exit=0)
        return record, source, log

    def test_valid_fresh_source(self):
        contract.validate_record(*self.sample(), pathlib.Path('/repo'))

    def test_exit_zero_error_is_not_pass(self):
        r, s, log = self.sample()
        log += 'Error: missing defining import\n'
        r['transcript'] = log
        with self.assertRaises(AssertionError): contract.validate_record(r, s, log, pathlib.Path('/repo'))

    def test_mutation_cannot_be_pass(self):
        r, s, log = self.sample(); r['targetMutationDetected'] = True
        with self.assertRaises(AssertionError): contract.validate_record(r, s, log, pathlib.Path('/repo'))

    def test_peak_must_match_retained_samples(self):
        r, s, log = self.sample(); r['maxSampleRSSKiB'] = 0
        with self.assertRaises(AssertionError): contract.validate_record(r, s, log, pathlib.Path('/repo'))

    def test_negative_needs_its_authenticated_symbol(self):
        r, s, log = self.sample(); log += 'Error: Mismatch between\n'
        r.update(transcript=log, exit=1, expectedDiagnostic='Mismatch between', symbol='wrongWitness')
        with self.assertRaises(AssertionError): contract.validate_record(r, s, log, pathlib.Path('/repo'))
        log += 'wrongWitness\n'; r['transcript'] = log
        contract.validate_record(r, s, log, pathlib.Path('/repo'))

    def test_no_target_building_is_not_fresh(self):
        r, s, log = self.sample(); r['transcript'] = ''
        with self.assertRaises(AssertionError): contract.validate_record(r, s, '', pathlib.Path('/repo'))

    def test_no_fourth_attempt(self):
        records = [dict(unit='A1-' + str(n), passed=False) for n in range(1, 5)]
        with self.assertRaises(AssertionError): contract.validate_attempts(records, {})

    def test_no_a_cap_extension(self):
        records = [dict(unit='A' + str(n) + '-1', passed=True) for n in range(1, 28)]
        with self.assertRaises(AssertionError): contract.validate_attempts(records, {})

    def test_no_inherited_successful_recheck_exception(self):
        records = [dict(unit='A' + str(n) + '-1', passed=True) for n in range(1, 9)]
        records.append(dict(unit='A8-2', passed=True))
        with self.assertRaises(AssertionError): contract.validate_attempts(records, {})

    def test_no_b_cap_extension(self):
        records = [dict(unit='B' + str(n) + '-1', passed=True) for n in range(1, 18)]
        with self.assertRaises(AssertionError): contract.validate_attempts(records, {})

    def test_no_noncontiguous_attempts(self):
        records = [dict(unit='A1-1', passed=False), dict(unit='A1-3', passed=True)]
        with self.assertRaises(AssertionError): contract.validate_attempts(records, {})

    def test_main_baseline_variants_allowed_not_other_worktrees(self):
        for path in ('research/DGamma/CP5AvailabilityAwarePlacement.idr', 'research/DGamma/CP5ActorLifecycleOnlyExtended.idr',
                     'research-tests/DGamma/R192ExtendedChildBlockProbe.idr', 'research/DGamma/CP5O20OwnCutSafetySpike.idr'):
            self.assertTrue(contract.owned_target(path))
        for path in ('../dgamma-lane2/research/DGamma/CP5L2R3Example.idr', '/Users/other/dgamma-lane2/research/DGamma/Example.idr',
                     'research/DGamma/../../outside.idr'):
            self.assertFalse(contract.owned_target(path))

if __name__ == '__main__':
    unittest.main()
