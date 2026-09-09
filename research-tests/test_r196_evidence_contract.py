"""Noncompiler regressions for R196 evidence rejection and approved exact deltas."""
import copy
import difflib
import hashlib
import importlib.util
import json
import pathlib
import subprocess
import unittest
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('contract',ROOT/'research-tests/r196_evidence_contract.py')
contract=importlib.util.module_from_spec(spec); spec.loader.exec_module(contract)

class Contracts(unittest.TestCase):
    def setUp(self):
        self.source=b'%default total\n'; self.path='research/DGamma/Example.idr'
        self.log='1/1: Building DGamma.Example ('+self.path+')\n'
        self.record=dict(path=self.path,sourceSHA256=hashlib.sha256(self.source).hexdigest(),transcript=self.log,rssSamples=[dict(rssKiB=100)],maxSampleRSSKiB=100,rssLimitKiB=200,passed=True,fresh=True,interrupted=False,targetMutationDetected=False,resourceStopped=False,unexpectedBuilding=[],expectedDiagnostic=None,exit=0)
    def valid(self,record=None,log=None):
        contract.validate_record(record or self.record,self.source,self.log if log is None else log,ROOT)
    def test_valid_positive(self): self.valid()
    def test_missing_own_building(self):
        r=copy.deepcopy(self.record); r['transcript']=''
        with self.assertRaises(AssertionError): self.valid(r,'')
    def test_empty_target_hash(self):
        with self.assertRaises(AssertionError): contract.validate_record(self.record,b'',self.log,ROOT)
    def test_resource_stop_not_pass(self):
        r=copy.deepcopy(self.record); r['resourceStopped']=True
        with self.assertRaises(AssertionError): self.valid(r)
    def test_mutation_not_pass(self):
        r=copy.deepcopy(self.record); r['targetMutationDetected']=True
        with self.assertRaises(AssertionError): self.valid(r)
    def test_unplanned_dependency_build_not_pass(self):
        r=copy.deepcopy(self.record); r['unexpectedBuilding']=['DGamma.Other']
        with self.assertRaises(AssertionError): self.valid(r)
    def test_lane2_not_owned(self):
        r=copy.deepcopy(self.record); r['path']='/Users/vyacheslavshebanov/Work/dgamma-lane2/research/DGamma/Example.idr'
        with self.assertRaises(AssertionError): self.valid(r)
    def test_sample_peak_authentication(self):
        r=copy.deepcopy(self.record); r['maxSampleRSSKiB']=0
        with self.assertRaises(AssertionError): self.valid(r)
    def test_order_rejects_missing_dependency(self):
        with self.assertRaises(AssertionError): contract.validate_topology([dict(unit='B1',path='consumer',dependencies=['producer'])],[])
    def test_approved_order(self):
        plan=json.loads((ROOT/'research-tests/O6-R196-DEPENDENT-RECHECK-PLAN.json').read_text())
        seen=contract.validate_topology(plan['items'],plan['unitAPaths'])
        self.assertEqual(len(seen),123)
        self.assertEqual(len(plan['excludedFromRunnableInventory']),124)
    def test_exact_approved_diffs(self):
        manifest=json.loads((ROOT/'research-tests/O6-R196-ROOT-CONTRACT-EXECUTION.json').read_text()); states={}
        for item in manifest['items']:
            path=item['path']
            before=states.get(path)
            if before is None: before=subprocess.check_output(['git','show',manifest['baselineCommit']+':'+path],cwd=ROOT,text=True)
            self.assertEqual(hashlib.sha256(before.encode()).hexdigest(),item['beforeSHA256'])
            after=contract.apply_manifest_diff(before,item['diff'])
            self.assertEqual(hashlib.sha256(after.encode()).hexdigest(),item['afterSHA256'])
            states[path]=after
    def test_append_only_A4_amendment(self):
        item=json.loads((ROOT/'research-tests/O6-R196-A4-SYNTAX-AMENDMENT.json').read_text())
        before=subprocess.check_output(['git','show','58f88c63:'+item['path']],cwd=ROOT,text=True)
        after=contract.apply_manifest_diff(before,item['diff'])
        self.assertEqual(hashlib.sha256(after.encode()).hexdigest(),item['afterSHA256'])
        original=json.loads((ROOT/'research-tests/O6-R196-ROOT-CONTRACT-EXECUTION.json').read_text())
        rejected=next(x for x in original['items'] if x['unit']=='A4')
        self.assertEqual(rejected['afterSHA256'],item['rejectedAfterSHA256'])
        self.assertNotEqual(rejected['afterSHA256'],item['afterSHA256'])
    def test_fields_match_R195_verbatim(self):
        manifest=(ROOT/'research-tests/O6-R195-ROOT-CONTRACT-MANIFEST.md').read_text()
        proposal=json.loads((ROOT/'research-tests/O6-R196-ROOT-CONTRACT-EXECUTION.json').read_text())
        for field,unit in [('operationalRootOrdinalPreserved','A2'),('deletionProducerRootOrdinalPreserved','A4')]:
            text='  0 '+field+' :'+manifest.split('  0 '+field+' :',1)[1].split('```',1)[0]
            delta=next(x['diff'] for x in proposal['items'] if x['unit']==unit)
            added=''.join(s[1:] for s in delta.splitlines(keepends=True) if s.startswith('+') and not s.startswith('+++'))
            self.assertIn(text,added)
    def test_diff_rejects_mutated_context(self):
        old='one\ntwo\n'; new='one\nthree\n'
        delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/source',tofile='b/source'))
        with self.assertRaises(AssertionError): contract.apply_manifest_diff('bad\ntwo\n',delta)

if __name__=='__main__': unittest.main()
