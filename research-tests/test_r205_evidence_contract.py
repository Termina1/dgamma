"""Mutation tests for exact-target, RSS, negative and import-closure evidence."""
import unittest,pathlib,hashlib,copy
from r205_evidence_contract import validate_record,validate_plan
class Evidence(unittest.TestCase):
    def setUp(self):
        self.root=pathlib.Path('/main');self.source=b'module DGamma.Test\n%default total\n'
        self.log='1/1: Building DGamma.Test (/main/research/DGamma/Test.idr)\n'
        self.r=dict(path='research/DGamma/Test.idr',sourceSHA256=hashlib.sha256(self.source).hexdigest(),transcript=self.log,buildingLines=['DGamma.Test (/main/research/DGamma/Test.idr)'],fresh=True,unexpectedBuilding=[],rssLimitKiB=48*1024*1024,rssSamples=[dict(timestampUTC='2',rssKiB=42,ownedPids=[7])],maxSampleRSSKiB=42,multipleOwnedCompilers=False,targetMutationDetected=False,mutatedPaths=[],expectedDiagnostic=None,symbol=None,exit=0,interrupted=False,resourceStopped=False,passed=True,start='1',end='3',crossLaneOverlapTimestampsUTC=[])
    def check(self):return validate_record(self.r,self.source,self.log,self.root)
    def test_positive(self):self.assertTrue(self.check())
    def test_source_mutation(self):
        self.source+=b'\n'
        with self.assertRaises(AssertionError):self.check()
    def test_stale_source(self):
        self.log='';self.r.update(transcript='',buildingLines=[])
        with self.assertRaises(AssertionError):self.check()
    def test_duplicate_build(self):
        self.log*=2;self.r['transcript']=self.log;self.r['buildingLines']*=2
        with self.assertRaises(AssertionError):self.check()
    def test_extra_dependency_build(self):
        self.log+='2/2: Building DGamma.Other (/main/research/DGamma/Other.idr)\n';self.r['transcript']=self.log;self.r['buildingLines'].append('DGamma.Other (/main/research/DGamma/Other.idr)')
        with self.assertRaises(AssertionError):self.check()
    def test_guard_not_raised(self):
        self.r['rssLimitKiB']=96*1024*1024
        with self.assertRaises(AssertionError):self.check()
    def test_peak_not_fudged(self):
        self.r['maxSampleRSSKiB']=41
        with self.assertRaises(AssertionError):self.check()
    def test_over_guard_not_pass(self):
        self.r['maxSampleRSSKiB']=self.r['rssSamples'][0]['rssKiB']=49*1024*1024
        with self.assertRaises(AssertionError):self.check()
    def test_two_compilers_not_pass(self):
        self.r['rssSamples'][0]['ownedPids']=[7,8];self.r['multipleOwnedCompilers']=True
        with self.assertRaises(AssertionError):self.check()
    def test_expected_negative(self):
        self.log+='Error: Mismatch between in someSymbol\n';self.r.update(transcript=self.log,exit=1,expectedDiagnostic='Mismatch between',symbol='someSymbol')
        self.assertTrue(self.check())
    def test_negative_missing_symbol(self):
        self.log+='Error: Mismatch between in wrongSymbol\n';self.r.update(transcript=self.log,exit=1,expectedDiagnostic='Mismatch between',symbol='someSymbol')
        with self.assertRaises(AssertionError):self.check()
    def test_negative_unexpected_success(self):
        self.r.update(expectedDiagnostic='Mismatch between',symbol='someSymbol')
        with self.assertRaises(AssertionError):self.check()
    def test_foreign_timestamp_only(self):
        self.r['crossLaneOverlapTimestampsUTC']=['2'];self.assertTrue(self.check())
    def test_outside_overlap_time(self):
        self.r['crossLaneOverlapTimestampsUTC']=['4']
        with self.assertRaises(AssertionError):self.check()
    def test_mutation_not_pass(self):
        self.r.update(targetMutationDetected=True,mutatedPaths=['src/DGamma/CP3.idr'])
        with self.assertRaises(AssertionError):self.check()
    def test_failed_compile_honest(self):
        self.log+='Error: type failure\n';self.r.update(transcript=self.log,exit=1,passed=False)
        self.assertFalse(self.check())
class Plan(unittest.TestCase):
    def setUp(self):
        self.sources={'src/DGamma/A.idr':b'module DGamma.A\n','research/DGamma/B.idr':b'module DGamma.B\nimport DGamma.A\n'}
        a=dict(path='src/DGamma/A.idr',module='DGamma.A',sourceSHA256=hashlib.sha256(self.sources['src/DGamma/A.idr']).hexdigest(),imports=[],dependencies=[])
        b=dict(path='research/DGamma/B.idr',module='DGamma.B',sourceSHA256=hashlib.sha256(self.sources['research/DGamma/B.idr']).hexdigest(),imports=['DGamma.A'],dependencies=['src/DGamma/A.idr'])
        self.plan=dict(allModulesTopological=[a,b],targets=[b],productionCount=1,researchFixtureCount=1)
    def check(self):return validate_plan(self.plan,self.sources.__getitem__)
    def test_complete(self):self.assertEqual(len(self.check()),2)
    def test_missing_dependency(self):
        self.plan['targets'][0]['dependencies']=[]
        with self.assertRaises(AssertionError):self.check()
    def test_wrong_order(self):
        self.plan['allModulesTopological'].reverse()
        with self.assertRaises(AssertionError):self.check()
    def test_omitted_target(self):
        self.plan['targets']=[]
        with self.assertRaises(AssertionError):self.check()
    def test_exact_source_override(self):
        path='research/DGamma/B.idr';before=hashlib.sha256(self.sources[path]).hexdigest();self.sources[path]+=b'-- explicit gated migration\n';after=hashlib.sha256(self.sources[path]).hexdigest()
        self.assertEqual(len(validate_plan(self.plan,self.sources.__getitem__,{path:dict(beforeSHA256=before,afterSHA256=after)})),2)
    def test_override_cannot_hide_wrong_prestate(self):
        path='research/DGamma/B.idr';after=hashlib.sha256(self.sources[path]).hexdigest()
        with self.assertRaises(AssertionError):validate_plan(self.plan,self.sources.__getitem__,{path:dict(beforeSHA256='wrong',afterSHA256=after)})
if __name__=='__main__': unittest.main()
