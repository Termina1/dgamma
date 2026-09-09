"""Compiler-free adversarial tests for the already-effective no-lock policy."""
import hashlib,importlib.util,json,pathlib,sys,unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('contract',ROOT/'research-tests/r200_evidence_contract.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.p=json.dumps(dict(authorization='SUPERVISOR RULE CHANGE: CROSS-LANE HEAVY LOCK ABOLISHED',runnerSHA256='new',shift='R200',oneCompilerPerLane=True)).encode()
        self.r=dict(unit='V12',start='2026-09-09T12:35:01+00:00',end='2026-09-09T12:35:04+00:00',runnerSHA256='new',executionPolicySHA256=hashlib.sha256(self.p).hexdigest(),crossLaneHeavyChecksPermitted=True,heavyLock=[],lane2Compilers=[],crossLaneOverlapTimestampsUTC=['2026-09-09T12:35:02+00:00'])
    def test_valid_new(self):c.validate_execution_policy(self.r,self.p)
    def test_valid_proof_invocation(self):
        self.r['unit']='B1-1';c.validate_execution_policy(self.r,self.p)
    def test_new_lock_rejected(self):
        self.r['heavyLock']=[dict(event='acquired')]
        with self.assertRaises(AssertionError):c.validate_execution_policy(self.r,self.p)
    def test_wrong_policy_hash_rejected(self):
        self.r['executionPolicySHA256']='wrong'
        with self.assertRaises(AssertionError):c.validate_execution_policy(self.r,self.p)
    def test_changed_runner_rejected(self):
        self.r['runnerSHA256']='different'
        with self.assertRaises(AssertionError):c.validate_execution_policy(self.r,self.p)
    def test_foreign_command_logging_rejected(self):
        self.r['lane2Compilers']=['foreign command']
        with self.assertRaises(AssertionError):c.validate_execution_policy(self.r,self.p)
    def test_non_timestamp_overlap_rejected(self):
        self.r['crossLaneOverlapTimestampsUTC']=[dict(pid=1)]
        with self.assertRaises(AssertionError):c.validate_execution_policy(self.r,self.p)
if __name__=='__main__':unittest.main(verbosity=2)
