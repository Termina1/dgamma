"""Compiler-free adversarial tests: evidence cannot launder stale/rejected checks.
maximum sampled RSS over command-matching idris2 processes (single-process compiler; not an aggregate process-tree total; not OS high-water).
"""
import hashlib, importlib.util, pathlib, sys, unittest
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('contract',ROOT/'research-tests/r204_evidence_contract.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)

class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.source=b'module DGamma.Test\n%default total\n'
        self.path='research/DGamma/Test.idr'
        self.log='1/1: Building DGamma.Test ('+str(ROOT/self.path)+')\n'
        self.r=dict(path=self.path,sourceSHA256=hashlib.sha256(self.source).hexdigest(),transcript=self.log,rssSamples=[dict(rssKiB=12)],maxSampleRSSKiB=12,rssLimitKiB=48*1024*1024,buildingLines=[self.log.split('Building ')[1].strip()],fresh=True,passed=True,interrupted=False,targetMutationDetected=False,resourceStopped=False,unexpectedBuilding=[],expectedDiagnostic=None,symbol=None,exit=0)
    def validate(self):c.validate_record(self.r,self.source,self.log,ROOT)
    def test_good(self):self.validate()
    def test_source_mutation(self):
        self.source+=b'x'
        with self.assertRaises(AssertionError):self.validate()
    def test_stale_no_building(self):
        self.log='';self.r['transcript']='';self.r['buildingLines']=[]
        with self.assertRaises(AssertionError):self.validate()
    def test_duplicate_own_building(self):
        self.log+=self.log;self.r['transcript']=self.log;self.r['buildingLines']*=2
        with self.assertRaises(AssertionError):self.validate()
    def test_wrong_source_same_module(self):
        self.log=self.log.replace('/research/','/other/');self.r['transcript']=self.log;self.r['buildingLines']=[self.log.split('Building ')[1].strip()]
        with self.assertRaises(AssertionError):self.validate()
    def test_unexpected_dependency_build(self):
        self.log+='2/2: Building DGamma.Other (/elsewhere/Other.idr)\n';self.r['transcript']=self.log;self.r['buildingLines'].append('DGamma.Other (/elsewhere/Other.idr)')
        with self.assertRaises(AssertionError):self.validate()
    def test_expected_negative(self):
        self.log+='Error: exact diagnostic in badSymbol\n';self.r.update(transcript=self.log,exit=1,expectedDiagnostic='exact diagnostic',symbol='badSymbol');self.validate()
    def test_negative_missing_symbol(self):
        self.log+='Error: exact diagnostic\n';self.r.update(transcript=self.log,exit=1,expectedDiagnostic='exact diagnostic',symbol='badSymbol')
        with self.assertRaises(AssertionError):self.validate()
    def test_nonzero_is_not_positive_pass(self):
        self.r['exit']=1
        with self.assertRaises(AssertionError):self.validate()
    def test_resource_stop_never_pass(self):
        self.r['resourceStopped']=True
        with self.assertRaises(AssertionError):self.validate()
    def test_exceeded_resource_limit(self):
        self.r['rssLimitKiB']=11
        with self.assertRaises(AssertionError):self.validate()
    def test_mutation_never_pass(self):
        self.r['targetMutationDetected']=True
        with self.assertRaises(AssertionError):self.validate()
    def test_false_memory_peak(self):
        self.r['maxSampleRSSKiB']=0
        with self.assertRaises(AssertionError):self.validate()
    def test_seeded_package_is_not_cold_claim(self):
        self.log='';self.r.update(path='package',transcript='',buildingLines=[]);self.validate()
    def test_declaration_delta(self):
        before=b'export\n0 law : Type\nlaw = ()\n';after=before+b'public export\nrecord Runtime where\n  constructor MkRuntime\n'
        self.assertEqual(c.declarations(after)-c.declarations(before),{'Runtime'})
    def test_missing_invalidated_import_rejected(self):
        source=b'module DGamma.A\nimport DGamma.B\n'
        item=dict(path='research/DGamma/A.idr',sourceHash=hashlib.sha256(source).hexdigest(),dependencies=[])
        with self.assertRaises(AssertionError):c.validate_plan([item],lambda _:source,{'DGamma.B':'research/DGamma/B.idr'},{'research/DGamma/B.idr'})
    def test_dependency_not_checked_before_consumer(self):
        source=b'module DGamma.A\nimport DGamma.B\n'
        item=dict(path='research/DGamma/A.idr',sourceHash=hashlib.sha256(source).hexdigest(),dependencies=['research/DGamma/B.idr'])
        with self.assertRaises(AssertionError):c.validate_plan([item],lambda _:source,{'DGamma.B':'research/DGamma/B.idr'},{'research/DGamma/B.idr'})
    def test_empty_snapshot_rejected_even_with_matching_hash(self):
        self.source=b'';self.r['sourceSHA256']=hashlib.sha256(self.source).hexdigest()
        with self.assertRaises(AssertionError):self.validate()
    def test_planned_import_outside_inventory_cannot_be_omitted(self):
        sources={'research/DGamma/A.idr':b'module DGamma.A\nimport DGamma.B\n','research/DGamma/B.idr':b'module DGamma.B\n'}
        plan=[dict(path=p,sourceHash=hashlib.sha256(sources[p]).hexdigest(),dependencies=[]) for p in ['research/DGamma/B.idr','research/DGamma/A.idr']]
        with self.assertRaises(AssertionError):c.validate_plan(plan,lambda p:sources[p],{'DGamma.B':'research/DGamma/B.idr'},set())
    def test_planned_import_outside_inventory_checks_topologically(self):
        sources={'research/DGamma/A.idr':b'module DGamma.A\nimport DGamma.B\n','research/DGamma/B.idr':b'module DGamma.B\n'}
        plan=[dict(path=p,sourceHash=hashlib.sha256(sources[p]).hexdigest(),dependencies=[] if p.endswith('B.idr') else ['research/DGamma/B.idr']) for p in ['research/DGamma/B.idr','research/DGamma/A.idr']]
        self.assertEqual(c.validate_plan(plan,lambda p:sources[p],{'DGamma.B':'research/DGamma/B.idr'},set()),set(sources))
    def test_source_changed_after_plan(self):
        item=dict(path='research/DGamma/A.idr',sourceHash='wrong',dependencies=[])
        with self.assertRaises(AssertionError):c.validate_plan([item],lambda _:b'module DGamma.A\n',{},set())

    def test_rejected_snapshot_authenticates_as_rejected(self):
        self.r['exit']=1;self.r['passed']=False;self.validate()
    def test_cannot_downgrade_success_to_hide_missing_receipt(self):
        self.r['passed']=False
        with self.assertRaises(AssertionError):self.validate()
    def test_only_exact_superseded_pass_cleanup(self):
        first=b'foo = bar\n\n'
        fixed=b'foo = bar\n'
        c.validate_superseded_pass(first,fixed)
        with self.assertRaises(AssertionError):c.validate_superseded_pass(first,fixed+b'changed')

    def test_rstrip_cleanup_cannot_change_code(self):
        with self.assertRaises(AssertionError):c.validate_superseded_pass(b'foo = bar\n\n',b'foo = baz\n')
    def test_style_repair_exact_statement_and_hashes(self):
        import subprocess
        before=subprocess.check_output(['git','show','9b532666:research-tests/DGamma/R203NativeDisappearancePositive.idr'],cwd=ROOT)
        after=(ROOT/'research-tests/DGamma/R203NativeDisappearancePositive.idr').read_bytes()
        c.validate_style_repair(before,after)
        with self.assertRaises(AssertionError):c.validate_style_repair(before,after.replace(b' :',b' : () ->',1))

    def test_p2_changes_only_exact_measurement_prose(self):
        import json,subprocess
        metric='maximum sampled RSS over command-matching idris2 processes (single-process compiler; not an aggregate process-tree total; not OS high-water)'
        path='research-tests/O6-R203-RESOURCE-AUDIT.json'
        before=json.loads(subprocess.check_output(['git','show','9b532666:'+path],cwd=ROOT)); after=json.loads((ROOT/path).read_bytes())
        before['sampleQualification']=metric+'; zero means no live sample captured, not zero actual peak'
        self.assertEqual(before,after)
        path='research-tests/O6-R203-GRIND-SHIFT-AUDIT.md'
        before=subprocess.check_output(['git','show','9b532666:'+path],cwd=ROOT).decode()
        expected=before.replace('These are one-second OWN-tree samples, NOT OS high-water; zeros are not measured peaks.', 'These report '+metric+'; zeros are not measured peaks.')
        self.assertNotEqual(expected,before); self.assertEqual(expected,(ROOT/path).read_text())

if __name__=='__main__':unittest.main(verbosity=2)
