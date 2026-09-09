#!/usr/bin/env python3
"""Copied from L2R14; compiler-free focused tests of the INDEPENDENT evidence validator, not
claims about Idris theorem truth or a replacement for parent-owned review.
"""
from pathlib import Path
import copy, importlib.util, unittest, sys, json
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('l2r15_verifier',Path(__file__).with_name('run-l2r15-independent-verify.py'))
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)

class EvidenceTests(unittest.TestCase):
 def setUp(self):
  self.path='research-tests/O6-L2R15-Sources/DGamma/L2R15Test.idr'
  self.source=b'module DGamma.L2R15Test\n%default total\npublic export\ndummy : Nat\ndummy = 0\n'
  self.log='1/1: Building DGamma.L2R15Test ('+str(v.ROOT/self.path)+')\n'
  self.r=dict(unit='A1-1',path=self.path,sourceSHA256=v.sha(self.source),transcript=self.log,buildingLines=self.log.splitlines(),buildingCount=1,fresh=True,expectedDiagnostic=None,exit=0,interrupted=False,sourceMutationObserved=False,passed=True,command=['idris2','--source-dir',str(v.ROOT/'src'),'--source-dir',str(v.ROOT/'research'),'--source-dir',str(v.ROOT/'research-tests'),'--source-dir',str((v.ROOT/self.path).parent.parent),'--check',str(v.ROOT/self.path)],targetMtimeTouch={'path':str(v.ROOT/self.path)},bundleSources=[],heavyLockAcquired=False,heavyLockEvents=[],maxSampleRSSKiB=1000,start='2026-09-09T12:00:00+00:00',end='2026-09-09T12:00:01+00:00',separateCompilerObservations=[],overlapTimestampsOnly=True)
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
  log=self.log.replace('L2R15Test','Wrong');r=copy.deepcopy(self.r);r.update(transcript=log,buildingLines=log.splitlines())
  with self.assertRaises(AssertionError):v.record_valid(r,self.source,log)
 def test_target_touch_only(self):self.rejects(targetMtimeTouch={'path':'/other'})
 def test_no_companion_bundle(self):self.rejects(bundleSources=[{}])
 def test_no_lock_acquisition(self):self.rejects(heavyLockAcquired=True)
 def test_no_lock_events(self):self.rejects(heavyLockEvents=['acquired'])
 def test_no_undeclared_heavy(self):self.rejects(declaredHeavy=True)
 def test_light_over_guard_must_interrupt(self):self.rejects(maxSampleRSSKiB=19*1024*1024)
 def test_foreign_compiler_is_never_owned(self):self.rejects(separateCompilerObservations=[dict(classification='lane2',command=str(v.ROOT)+'/file')])
 def test_foreign_metadata_rejected(self):
  self.rejects(separateCompilerObservations=[dict(classification='foreign',command='/foreign/compiler')])
 def test_compiler_target_fixed(self):self.rejects(command=['idris2','--check','/wrong'])
 def test_no_foreign_source_root(self):
  command=list(self.r['command']);command[2]='/foreign/src';self.rejects(command=command)
 def test_no_package_build(self):self.rejects(command=['idris2','--build','package','--check',str(v.ROOT/self.path)])
 def test_timing_order(self):self.rejects(end='2026-09-09T11:00:00+00:00')
 def test_protected_path(self):self.assertFalse(v.path_allowed('src/DGamma/CP3.idr'))
 def test_other_predecessor_path(self):self.assertFalse(v.path_allowed('research-tests/O6-L2R9-Sources/DGamma/Other.idr'))
 def test_path_traversal(self):self.assertFalse(v.path_allowed('research-tests/O6-L2R15-Sources/../../src/DGamma/X.idr'))
 def test_absolute_path(self):self.assertFalse(v.path_allowed(str(v.ROOT/self.path)))
 def test_no_predecessor_bootstrap(self):self.assertFalse(v.path_allowed("research-tests/O6-L2R12-Sources/DGamma/L2R12PhaseAccepted.idr"))
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

 def test_missing_timestamp_only_marker_rejected(self):self.rejects(overlapTimestampsOnly=False)
 def test_eof_whitespace_rejected(self):
  data=self.source+b'\n';r=copy.deepcopy(self.r);r['sourceSHA256']=v.sha(data)
  with self.assertRaises(AssertionError):v.record_valid(r,data,self.log)
 def test_record_status_neutral(self):self.assertEqual(v.type_status(True),'checked TYPE declaration; inhabitance reported separately')
 def test_alias_status_not_inhabited(self):self.assertEqual(v.type_status(False),'checked TYPE declaration; NOT inhabited')
 def test_type_record_distinction(self):self.assertNotEqual(v.type_status(True),v.type_status(False))
 def test_kind_record(self):self.assertEqual(v.declaration_kind(b'record Packet where\n  field : Nat\n','Packet'),'type')
 def test_kind_alias(self):self.assertEqual(v.declaration_kind(b'Obligation : Type\nObligation = Nat\n','Obligation'),'type')
 def test_kind_erased_proof(self):self.assertEqual(v.declaration_kind(b'0 lemma : 0 = 0\nlemma = Refl\n','lemma'),'proof')
 def test_kind_executable(self):self.assertEqual(v.declaration_kind(b'run : Nat\nrun = 0\n','run'),'executable')

 def test_protected_module_name_in_lane_directory(self):self.assertFalse(v.path_allowed('research-tests/O6-L2R15-Sources/DGamma/CP3.idr'))
 def test_module_header_must_match_target(self):
  data=self.source.replace(b'module DGamma.L2R15Test',b'module DGamma.CP3');r=copy.deepcopy(self.r);r['sourceSHA256']=v.sha(data)
  with self.assertRaises(AssertionError):v.record_valid(r,data,self.log)
 def test_data_type_status_is_not_inhabitance(self):self.assertEqual(v.declaration_kind(b'data Path : Type where\n  Here : Path\n','Path'),'type')
 def test_l2r14_path_rejected(self):self.assertFalse(v.path_allowed('research-tests/O6-L2R14-Sources/DGamma/L2R14PhaseOrigins.idr'))


 def patch_fixture(self):return 'a\nb\nc\n','--- a/src/DGamma/CP3.idr\n+++ b/src/DGamma/CP3.idr\n@@ -1,3 +1,3 @@\n a\n-b\n+B\n c\n'
 def test_tier1_patch_apply_in_memory(self):
  base,patch=self.patch_fixture();self.assertEqual(v.apply_tier1_patch(base,patch),'a\nB\nc\n')
 def test_tier1_patch_other_file_rejected(self):
  base,patch=self.patch_fixture()
  with self.assertRaises(AssertionError):v.apply_tier1_patch(base,patch.replace('CP3.idr','CP4.idr'))
 def test_tier1_patch_context_rejected(self):
  base,patch=self.patch_fixture()
  with self.assertRaises(AssertionError):v.apply_tier1_patch(base,patch.replace(' a\n',' x\n'))
 def test_tier1_patch_old_count_rejected(self):
  base,patch=self.patch_fixture()
  with self.assertRaises(AssertionError):v.apply_tier1_patch(base,patch.replace('-1,3','-1,4'))
 def test_tier1_patch_new_count_rejected(self):
  base,patch=self.patch_fixture()
  with self.assertRaises(AssertionError):v.apply_tier1_patch(base,patch.replace('+1,3','+1,4'))
 def test_tier1_patch_overlap_rejected(self):
  base,patch=self.patch_fixture()
  with self.assertRaises(AssertionError):v.apply_tier1_patch(base,patch+'@@ -1,1 +4,1 @@\n a\n')
 def test_tier1_patch_missing_hunk_rejected(self):
  base,patch=self.patch_fixture()
  with self.assertRaises(AssertionError):v.apply_tier1_patch(base,'\n'.join(patch.splitlines()[:2])+'\n')
 def test_tier1_patch_stray_line_rejected(self):
  base,patch=self.patch_fixture()
  with self.assertRaises(AssertionError):v.apply_tier1_patch(base,patch+'garbage\n')
 def test_tier1_patch_old_position_rejected(self):
  base,patch=self.patch_fixture()
  with self.assertRaises(AssertionError):v.apply_tier1_patch(base,patch.replace('-1,3','-0,3'))
 def test_tier1_patch_new_position_rejected(self):
  base,patch=self.patch_fixture()
  with self.assertRaises(AssertionError):v.apply_tier1_patch(base,patch.replace('+1,3','+2,3'))


 def test_standdown_guard_precedes_launcher_spawn(self):
  code=Path(__file__).with_name('run-l2r15-launch.py').read_text()
  self.assertLess(code.index("assert not (ROOT/'research-tests/O6-L2R15-POST-GATE-STANDDOWN.json')"),code.index('subprocess.Popen'))
 def test_standdown_guard_precedes_checker_spawn(self):
  code=Path(__file__).with_name('run-l2r15-check.py').read_text()
  self.assertLess(code.index("assert not (ROOT/'research-tests/O6-L2R15-POST-GATE-STANDDOWN.json')"),code.index('subprocess.Popen'))
 def test_actual_signed_patch_is_only_in_memory(self):
  base=(v.ROOT/'src/DGamma/CP3.idr').read_bytes()
  patch=(v.ROOT/(v.PREFIX+'CP3-TIER1-SIGNED-DIFF.patch')).read_text()
  inventory=json.loads((v.ROOT/(v.PREFIX+'CP3-REBUILD-INVENTORY.json')).read_text())
  candidate=v.apply_tier1_patch(base.decode(),patch)
  self.assertEqual(v.sha(candidate.encode()),inventory['candidateSHA256'])
  self.assertEqual((v.ROOT/'src/DGamma/CP3.idr').read_bytes(),base)
  self.assertFalse(inventory['typecheckedInCP3'])

if __name__=='__main__':unittest.main(verbosity=2)
