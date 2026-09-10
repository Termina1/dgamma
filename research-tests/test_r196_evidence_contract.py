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
    def test_original_plan_omits_required_invalidated_import(self):
        plan=json.loads((ROOT/'research-tests/O6-R196-DEPENDENT-RECHECK-PLAN.json').read_text())
        inventory=json.loads((ROOT/'research-tests/O6-R195-ROOT-CONTRACT-COSTS.json').read_text())
        included={x['path'] for x in plan['items']}|set(plan['unitAPaths'])
        modules={x['module']:x['path'] for x in inventory['entries']}
        with self.assertRaises(AssertionError):
            contract.validate_import_closed(included,modules,lambda p:(ROOT/p).read_text())
    def test_continuation_is_import_closed_and_topological(self):
        plan=json.loads((ROOT/'research-tests/O6-R196-DEPENDENT-RECHECK-CONTINUATION.json').read_text())
        inventory=json.loads((ROOT/'research-tests/O6-R195-ROOT-CONTRACT-COSTS.json').read_text())
        included=contract.validate_topology(plan['items'],plan['unitAPaths'])
        self.assertEqual(len(included),136)
        self.assertEqual(len(plan['excludedFromRunnableInventory']),111)
        modules={x['module']:x['path'] for x in inventory['entries']}
        contract.validate_import_closed(included,modules,lambda p:(ROOT/p).read_text())
    def test_second_window_has_no_missing_invalidated_predecessor(self):
        plan=json.loads((ROOT/'research-tests/O6-R196-SECOND-WINDOW-PLAN.json').read_text())
        former=json.loads((ROOT/'research-tests/O6-R196-DEPENDENT-RECHECK-CONTINUATION.json').read_text())
        affected={x['path'] for x in plan['items']}
        unaffected=({x['path'] for x in former['items']}|set(former['unitAPaths']))-affected
        unaffected.add(plan['helperPath'])
        contract.validate_topology(plan['items'],unaffected)
        self.assertEqual(len(plan['items']),127)
        self.assertNotIn('research/DGamma/CP5ConfluenceLocalDiamondSpike.idr',affected)
        self.assertNotIn('research/DGamma/CP5UniqueRawNameOrdinalCapital.idr',affected)
    def test_helper_amendment_only_adds_the_approved_proof(self):
        helper=json.loads((ROOT/'research-tests/O6-R196-C3-DELETION-HELPER-MANIFEST.json').read_text())
        earlier=json.loads((ROOT/'research-tests/O6-R196-A4-SYNTAX-AMENDMENT.json').read_text())
        base=subprocess.check_output(['git','show','58f88c63:'+helper['path']],cwd=ROOT,text=True)
        before=contract.apply_manifest_diff(base,earlier['diff'])
        after=contract.apply_manifest_diff(before,helper['diff'])
        self.assertEqual(hashlib.sha256(before.encode()).hexdigest(),helper['beforeSHA256'])
        self.assertEqual(hashlib.sha256(after.encode()).hexdigest(),helper['afterSHA256'])
        self.assertEqual(after.replace(helper['helper'],''),before)
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
