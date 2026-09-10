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
if __name__=='__main__':unittest.main(verbosity=2)
