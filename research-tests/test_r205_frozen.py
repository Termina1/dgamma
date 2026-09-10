"""Adversarial tests for committed-vs-proposed frozen-baseline authorization."""
import copy,json,pathlib,tempfile,unittest
from unittest.mock import patch
import r205_common as common

class FrozenGateTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=pathlib.Path(self.temp.name);(self.root/'research-tests').mkdir()
        self.path='research/DGamma/CP5ConfluenceCanonicalSortSpike.idr'
        self.pre=dict(protectedModuleHashes={self.path:'before'},regions={'O19':'unchanged'},holeStatements={'sort':'whole declaration/body'},census=[1,2,0,0,1])
        (self.root/'research-tests/O6-R205-PRE-STATE.json').write_text(json.dumps({'frozen':self.pre}))
        self.gate=dict(path=self.path,beforeSHA256='before',afterSHA256='after',status='APPROVED exact diff')
    def tearDown(self):self.temp.cleanup()
    def check(self,current,gate=True):
        if gate:(self.root/'research-tests/O6-R205-FROZEN-MIGRATION-GATE.json').write_text(json.dumps(self.gate))
        with patch.object(common,'ROOT',self.root),patch.object(common,'frozen',return_value=current):common.assert_frozen()
    def after(self):
        current=copy.deepcopy(self.pre);current['protectedModuleHashes'][self.path]='after';return current
    def test_no_gate_exact_prestate(self):self.check(copy.deepcopy(self.pre),False)
    def test_proposal_allows_before_apply(self):self.check(copy.deepcopy(self.pre))
    def test_approved_exact_candidate(self):self.check(self.after())
    def test_committed_exact_candidate(self):
        self.gate['status']='COMMITTED abc';self.check(self.after())
    def test_committed_cannot_revert_to_prestate(self):
        self.gate['status']='COMMITTED abc'
        with self.assertRaises(AssertionError):self.check(copy.deepcopy(self.pre))
    def test_approved_source_hash_does_not_authorize_hole_edit(self):
        current=self.after();current['holeStatements']['sort']='changed'
        with self.assertRaises(AssertionError):self.check(current)
    def test_approved_source_hash_does_not_authorize_region_edit(self):
        current=self.after();current['regions']['O19']='changed'
        with self.assertRaises(AssertionError):self.check(current)
    def test_wrong_prestate_gate_rejected(self):
        self.gate['beforeSHA256']='wrong'
        with self.assertRaises(AssertionError):self.check(self.after())
    def test_unapproved_candidate_rejected(self):
        self.gate['status']='PROPOSAL only'
        with self.assertRaises(AssertionError):self.check(self.after())

if __name__=='__main__':unittest.main()
