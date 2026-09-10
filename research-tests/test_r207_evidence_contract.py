import copy, hashlib, pathlib, unittest
from r207_evidence_contract import validate_record

class ReceiptContract(unittest.TestCase):
    def setUp(self):
        self.root=pathlib.Path('/review')
        self.source=b'module DGamma.Test\n%default total\n'
        self.line='DGamma.Test (/review/research/DGamma/Test.idr)'
        self.text='1/1: Building '+self.line+'\n'
        self.r=dict(path='research/DGamma/Test.idr',sourceSHA256=hashlib.sha256(self.source).hexdigest(),transcript=self.text,buildingLines=[self.line],fresh=True,unexpectedBuilding=[],rssSamples=[dict(rssKiB=100)],maxSampleRSSKiB=100,rssLimitKiB=48*1024*1024,exit=0,expectedDiagnostic=None,symbol=None,passed=True,interrupted=False,resourceStopped=False,targetMutationDetected=False,multipleOwnedCompilers=False,start='2026-09-10T02:10:00',end='2026-09-10T02:10:01',crossLaneOverlapTimestampsUTC=[],CP3Blob='eeaa70aa4414648bb2a1173d58244267997d16d7')
    def valid(self): return validate_record(self.r,self.source,self.text,self.root)
    def rejects(self):
        with self.assertRaises(AssertionError): self.valid()
    def test_positive(self): self.assertTrue(self.valid())
    def test_source_hash(self): self.source+=b'-- changed\n';self.rejects()
    def test_transcript(self): self.text+='Error: forged\n';self.rejects()
    def test_missing_own_build(self): self.r['buildingLines']=[];self.rejects()
    def test_dependency_build(self):
        self.text='1/2: Building DGamma.Dependency (/review/research/DGamma/Dependency.idr)\n2/2: Building '+self.line+'\n'
        self.r['transcript']=self.text
        self.r['buildingLines']=['DGamma.Dependency (/review/research/DGamma/Dependency.idr)',self.line]
        self.rejects()
    def test_exit(self): self.r['exit']=1;self.rejects()
    def test_mutation(self): self.r['targetMutationDetected']=True;self.rejects()
    def test_multiple_own(self): self.r['multipleOwnedCompilers']=True;self.rejects()
    def test_resource(self): self.r['rssSamples'][0]['rssKiB']=49*1024*1024;self.r['maxSampleRSSKiB']=49*1024*1024;self.rejects()
    def test_forged_peak(self): self.r['maxSampleRSSKiB']=0;self.rejects()
    def test_negative_requires_symbol(self):
        self.text+='Error: exact expected diagnostic\n';self.r.update(transcript=self.text,exit=1,expectedDiagnostic='exact expected diagnostic',symbol='missingGoal')
        self.rejects()
    def test_exact_negative(self):
        self.text+='Error: exact expected diagnostic at wantedGoal\n';self.r.update(transcript=self.text,exit=1,expectedDiagnostic='exact expected diagnostic',symbol='wantedGoal')
        self.assertTrue(self.valid())
    def test_package_is_seeded_not_fresh_source(self):
        self.r.update(path='package',transcript='',buildingLines=[],unexpectedBuilding=[]);self.text=''
        self.assertTrue(self.valid())
    def test_package_rebuild_not_accepted(self): self.r['path']='package';self.rejects()
    def test_overlap_timestamp_only(self): self.r['crossLaneOverlapTimestampsUTC']=['2026-09-10T02:10:00.5'];self.assertTrue(self.valid())
    def test_overlap_outside_interval(self): self.r['crossLaneOverlapTimestampsUTC']=['2026-09-10T02:12:00'];self.rejects()
    def test_production_blob(self): self.r['CP3Blob']='old-baseline';self.rejects()
    def test_resource_stop_flag(self): self.r['resourceStopped']=True;self.rejects()

if __name__=='__main__': unittest.main()
