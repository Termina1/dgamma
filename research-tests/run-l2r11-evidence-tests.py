#!/usr/bin/env python3
"""Compiler-free focused tests of the INDEPENDENT evidence validator, not
claims about Idris theorem truth or a replacement for parent-owned review.
"""
from pathlib import Path
import copy, importlib.util, unittest
spec=importlib.util.spec_from_file_location('l2r11_verifier',Path(__file__).with_name('run-l2r11-independent-verify.py'))
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)

class EvidenceTests(unittest.TestCase):
 def setUp(self):
  self.path='research-tests/O6-L2R11-Sources/DGamma/L2R11Test.idr'
  self.source=b'module DGamma.L2R11Test\n%default total\npublic export\ndummy : Nat\ndummy = 0\n'
  self.log='1/1: Building DGamma.L2R11Test ('+str(v.ROOT/self.path)+')\n'
  self.r=dict(unit='A1-1',path=self.path,sourceSHA256=v.sha(self.source),transcript=self.log,buildingLines=self.log.splitlines(),buildingCount=1,fresh=True,expectedDiagnostic=None,exit=0,interrupted=False,sourceMutationObserved=False,passed=True,command=['idris2','--check',str(v.ROOT/self.path)],targetMtimeTouch={'path':str(v.ROOT/self.path)},bundleSources=[],heavyLockAcquired=False,heavyLockEvents=[],maxSampleRSSKiB=1000,start='2026-09-09T12:00:00+00:00',end='2026-09-09T12:00:01+00:00',separateCompilerObservations=[])
 def rejects(self,**changes):
  r=copy.deepcopy(self.r);r.update(changes)
  with self.assertRaises(AssertionError):v.record_valid(r,self.source,self.log)
 def test_valid_fresh_record(self):self.assertTrue(v.record_valid(self.r,self.source,self.log))
 def test_exact_source_hash(self):self.rejects(sourceSHA256='0'*64)
 def test_exact_transcript(self):self.rejects(transcript='')
 def test_failed_exit_not_pass(self):self.rejects(exit=1)
 def test_interrupted_not_pass(self):self.rejects(interrupted=True)
 def test_mutated_not_pass(self):self.rejects(sourceMutationObserved=True)
 def test_expected_diagnostic_not_accepted(self):self.rejects(expectedDiagnostic='Error')
 def test_old_or_missing_fresh_flag(self):self.rejects(fresh=False)
 def test_extra_building_line(self):
  log=self.log+'2/2: Building DGamma.Other (/bad/path.idr)\n';r=copy.deepcopy(self.r);r.update(transcript=log,buildingLines=log.splitlines(),buildingCount=2)
  with self.assertRaises(AssertionError):v.record_valid(r,self.source,log)
 def test_build_count_is_not_denominator(self):
  log=self.log.replace('1/1:','3/3:');r=copy.deepcopy(self.r);r.update(transcript=log,buildingLines=log.splitlines())
  self.assertTrue(v.record_valid(r,self.source,log))
 def test_wrong_target_build(self):
  log=self.log.replace('L2R11Test','Wrong');r=copy.deepcopy(self.r);r.update(transcript=log,buildingLines=log.splitlines())
  with self.assertRaises(AssertionError):v.record_valid(r,self.source,log)
 def test_target_touch_only(self):self.rejects(targetMtimeTouch={'path':'/other'})
 def test_no_companion_bundle(self):self.rejects(bundleSources=[{}])
 def test_no_lock_acquisition(self):self.rejects(heavyLockAcquired=True)
 def test_no_lock_events(self):self.rejects(heavyLockEvents=['acquired'])
 def test_no_undeclared_heavy(self):self.rejects(declaredHeavy=True)
 def test_light_over_guard_must_interrupt(self):self.rejects(maxSampleRSSKiB=19*1024*1024)
 def test_foreign_compiler_is_never_owned(self):self.rejects(separateCompilerObservations=[dict(classification='lane2',command=str(v.ROOT)+'/file')])
 def test_foreign_compiler_separate(self):
  self.r['separateCompilerObservations']=[dict(classification='main-lane compiler (separate worktree)',command='/Users/vyacheslavshebanov/Work/dgamma/other.idr')]
  self.assertTrue(v.record_valid(self.r,self.source,self.log))
 def test_compiler_target_fixed(self):self.rejects(command=['idris2','--check','/wrong'])
 def test_no_package_build(self):self.rejects(command=['idris2','--build','package','--check',str(v.ROOT/self.path)])
 def test_timing_order(self):self.rejects(end='2026-09-09T11:00:00+00:00')
 def test_protected_path(self):self.assertFalse(v.path_allowed('src/DGamma/CP3.idr'))
 def test_other_predecessor_path(self):self.assertFalse(v.path_allowed('research-tests/O6-L2R9-Sources/DGamma/Other.idr'))
 def test_path_traversal(self):self.assertFalse(v.path_allowed('research-tests/O6-L2R11-Sources/../../src/DGamma/X.idr'))
 def test_absolute_path(self):self.assertFalse(v.path_allowed(str(v.ROOT/self.path)))
 def test_exact_bootstrap_target(self):self.assertTrue(v.path_allowed(v.BOOTSTRAP))
 def test_declaration_parser(self):self.assertEqual(v.decls(b'0 lemma : Nat\nlemma=0\nrecord Packet where\n  field : Nat\ndata Kind : Type where\n  One : Kind\n'),{'lemma','Packet','Kind'})
 def test_comment_repair_body_preserved(self):
  self.assertEqual(v.code(b'||| old\n0 p : Nat\np = 0\n'),v.code(b'||| new\n||| explanation\n0 p : Nat\np = 0\n'))
 def test_comment_not_escape(self):
  data=b'||| with let partial describe forbidden forms only\n'+self.source;r=copy.deepcopy(self.r);r['sourceSHA256']=v.sha(data)
  self.assertTrue(v.record_valid(r,data,self.log))
 def test_real_escape_rejected(self):
  data=self.source+b'bad : Nat\nbad = believe_me 0\n';r=copy.deepcopy(self.r);r['sourceSHA256']=v.sha(data)
  with self.assertRaises(AssertionError):v.record_valid(r,data,self.log)
 def test_trailing_whitespace_rejected(self):
  data=self.source+b'\n  \n';r=copy.deepcopy(self.r);r['sourceSHA256']=v.sha(data)
  with self.assertRaises(AssertionError):v.record_valid(r,data,self.log)

 def test_bootstrap_only_v0(self):
  self.r['path']=v.BOOTSTRAP
  with self.assertRaises(AssertionError):v.record_valid(self.r,self.source,self.log)
 def test_erased_hole_rejected(self):
  data=self.source+b'0 hole : Nat\nhole = ?unfinished\n';r=copy.deepcopy(self.r);r['sourceSHA256']=v.sha(data)
  with self.assertRaises(AssertionError):v.record_valid(r,data,self.log)
 def test_timestamp_only_overlap(self):
  self.r['overlapTimestampsOnly']=True
  self.r['separateCompilerObservations']=[dict(firstObservedUTC=self.r['start'],lastObservedUTC=self.r['end'])]
  self.assertTrue(v.record_valid(self.r,self.source,self.log))
 def test_timestamp_only_rejects_extra_fields(self):
  self.r['overlapTimestampsOnly']=True
  self.rejects(separateCompilerObservations=[dict(firstObservedUTC=self.r['start'],lastObservedUTC=self.r['end'],pid=1)])
 def test_timestamp_overlap_bounds(self):
  self.r['overlapTimestampsOnly']=True
  self.rejects(separateCompilerObservations=[dict(firstObservedUTC='2026-09-09T11:00:00+00:00',lastObservedUTC=self.r['end'])])

if __name__=='__main__':unittest.main(verbosity=2)
