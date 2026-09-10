#!/usr/bin/env python3
"""L2R16 isolated compiler-free evidence contract tests. Adapted from L2R15
adversarial verification tests; exercises freshness, RSS, scope, source bytes,
overlap privacy and TYPE-vs-inhabitant distinctions. No native compiler.
"""
import copy,importlib.util,json,pathlib,sys,unittest
sys.dont_write_bytecode=True
P=pathlib.Path(__file__).with_name('run-l2r16-independent-verify.py')
spec=importlib.util.spec_from_file_location('l2r16_verifier',P);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
PATH='research-tests/O6-L2R16-Sources/DGamma/L2R16Probe.idr'
DATA=b'module DGamma.L2R16Probe\n\n%default total\n\n0 equal : Z = Z\nequal = Refl\n'
LOG='1/1: Building DGamma.L2R16Probe ('+str(v.ROOT/PATH)+')\n'
def example():
 return dict(path=PATH,sourceSHA256=v.sha(DATA),transcript=LOG,buildingLines=LOG.splitlines(),buildingCount=1,fresh=True,passed=True,exit=0,interrupted=False,sourceMutationObserved=False,expectedDiagnostic=None,bundleSources=[],command=['idris2','--source-dir',str(v.ROOT/'research-tests/O6-L2R16-Sources'),'--check',str(v.ROOT/PATH)],targetMtimeTouch=dict(path=str(v.ROOT/PATH)),rssLimitKiB=18*1024*1024,declaredHeavy=False,maxSampleRSSKiB=1234,overlapTimestampsOnly=True,separateCompilerObservations=[],start='2026-09-10T03:00:00+00:00',end='2026-09-10T03:00:01+00:00')
class EvidenceContract(unittest.TestCase):
 def test_fresh_own_target_pass(self):self.assertTrue(v.record_valid(example(),DATA,LOG,[]))
 def test_extra_dependency_cannot_claim_pass(self):
  r=example();log='1/2: Building DGamma.Dependency (/x)\n'+LOG;r.update(transcript=log,buildingLines=log.splitlines(),buildingCount=2)
  with self.assertRaises(AssertionError):v.record_valid(r,DATA,log,[])
 def test_cache_only_cannot_claim_fresh(self):
  r=example();r.update(transcript='',buildingLines=[],buildingCount=0)
  with self.assertRaises(AssertionError):v.record_valid(r,DATA,'',[])
 def test_mutated_source_rejected(self):
  with self.assertRaises(AssertionError):v.record_valid(example(),DATA+b'\n',LOG,[])
 def test_whitespace_rejected_even_with_new_digest(self):
  r=example();data=DATA+b'\n';r['sourceSHA256']=v.sha(data)
  with self.assertRaises(AssertionError):v.record_valid(r,data,LOG,[])
 def test_over_guard_cannot_pass(self):
  r=example();r['maxSampleRSSKiB']=r['rssLimitKiB']+1
  with self.assertRaises(AssertionError):v.record_valid(r,DATA,LOG,[])
 def test_foreign_pid_metadata_rejected(self):
  r=example();r['separateCompilerObservations']=[dict(pid=1,firstObservedUTC=r['start'],lastObservedUTC=r['end'])]
  with self.assertRaises(AssertionError):v.record_valid(r,DATA,LOG,[])
 def test_timestamp_only_overlap_accepted(self):
  r=example();r['separateCompilerObservations']=[dict(firstObservedUTC=r['start'],lastObservedUTC=r['end'])]
  self.assertTrue(v.record_valid(r,DATA,LOG,[]))
 def test_source_scope(self):
  self.assertFalse(v.source_allowed('src/DGamma/CP3.idr',[]))
  self.assertTrue(v.source_allowed(PATH,[]))
 def test_type_status_is_not_inhabitation(self):
  self.assertIn('inhabitance reported separately',v.type_status(True))
  self.assertIn('NOT an inhabitant',v.type_status(False))
 def test_declarations_ignore_record_fields(self):
  data=b'record Packet where\n  field : Nat\nvalue : Nat\nvalue = Z\n'
  self.assertEqual(v.decls(data),{'Packet','value'})
 def test_nonzero_exit_cannot_claim_pass(self):
  r=example();r['exit']=1
  with self.assertRaises(AssertionError):v.record_valid(r,DATA,LOG,[])
 def test_unsafe_body_rejected_even_with_matching_hash(self):
  data=DATA.replace(b'equal = Refl',b'equal = believe_me Refl');r=example();r['sourceSHA256']=v.sha(data)
  with self.assertRaises(AssertionError):v.record_valid(r,data,LOG,[])
 def test_new_hole_rejected(self):
  data=DATA.replace(b'equal = Refl',b'equal = ?proof');r=example();r['sourceSHA256']=v.sha(data)
  with self.assertRaises(AssertionError):v.record_valid(r,data,LOG,[])
 def test_new_with_construct_rejected(self):
  data=DATA+b'other = with value\n';r=example();r['sourceSHA256']=v.sha(data)
  with self.assertRaises(AssertionError):v.record_valid(r,data,LOG,[])
 def test_visibility_only_exact_gate(self):
  before=b'export\n0 equal : Z = Z\nequal = Refl\n';after=before.replace(b'export',b'public export',1)
  gate=dict(beforeSHA256=v.sha(before),afterSHA256=v.sha(after),oldText='export\n0 equal',newText='public export\n0 equal')
  self.assertTrue(v.visibility_only(before,after,gate))
 def test_visibility_gate_rejects_body_change_even_with_updated_digest(self):
  before=b'export\n0 equal : Z = Z\nequal = Refl\n';after=before.replace(b'export',b'public export',1).replace(b'equal = Refl',b'equal = anotherProof')
  gate=dict(beforeSHA256=v.sha(before),afterSHA256=v.sha(after),oldText='export\n0 equal',newText='public export\n0 equal')
  with self.assertRaises(AssertionError):v.visibility_only(before,after,gate)
 def test_preflight_consumes_missing_request(self):self.assertTrue(v.bounded_requests([1,3],[2],3))
 def test_preflight_does_not_allow_fourth_attempt(self):
  with self.assertRaises(AssertionError):v.bounded_requests([1,3,4],[2],3)
 def test_request_id_cannot_be_reused(self):
  with self.assertRaises(AssertionError):v.bounded_requests([1,2],[2],3)
 def test_missing_request_requires_evidence(self):
  with self.assertRaises(AssertionError):v.bounded_requests([1,3],[],3)
 def test_interrupted_buffered_no_build_is_failure_not_fake_receipt(self):
  r=example();r.update(transcript='',buildingLines=[],buildingCount=0,fresh=False,passed=False,exit=-15,interrupted=True,maxSampleRSSKiB=r['rssLimitKiB']+100)
  self.assertFalse(v.record_valid(r,DATA,'',[]))
 def test_deadline_interruption_cannot_pass(self):
  r=example();r.update(deadlineInterrupted=True,deadlineStopUTC=r['start'])
  with self.assertRaises(AssertionError):v.record_valid(r,DATA,LOG,[])
if __name__=='__main__':unittest.main(verbosity=2)
