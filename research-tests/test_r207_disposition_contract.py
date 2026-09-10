import unittest
from r207_disposition_contract import classify_module, needs_dependency_refresh

class DispositionContract(unittest.TestCase):
    def setUp(self):
        self.r=dict(passed=True,fresh=True,unexpectedBuilding=[],end='2026-09-10T04:00:00',exit=0)
        self.args=dict(exact=True,record=self.r,epoch='2026-09-10T03:00:00',blocked=False,
                       in_closure=True,baseline_status='passed',seed_authenticated=True)
    def result(self): return classify_module(**self.args)
    def test_current_success(self): self.assertEqual(self.result(),('fresh PASS',True))
    def test_expected_negative_is_not_importable(self):
        self.r['exit']=1
        self.assertEqual(self.result(),('fresh expected-negative PASS',False))
    def test_failed_native_cannot_fallback_to_seed(self):
        self.args['in_closure']=False;self.r['passed']=False
        self.assertEqual(self.result(),('fresh own-target FAILED',False))
    def test_rejected_cache_check_cannot_revive_seed(self):
        self.args['in_closure']=False;self.r.update(passed=False,fresh=False)
        self.assertEqual(self.result(),('rejected native invocation / cache-resource gate',False))
    def test_false_pass_flag_without_own_build(self):
        self.r['fresh']=False
        self.assertEqual(self.result(),('rejected native invocation / cache-resource gate',False))
    def test_blocked_import_overrides_own_pass(self):
        self.args['blocked']=True
        self.assertEqual(self.result(),('blocked by untrusted/retired import',False))
    def test_predates_dependency_change(self):
        self.args['epoch']='2026-09-10T05:00:00'
        self.assertEqual(self.result(),('unchecked / invalidated',False))
    def test_unchanged_seed_is_explicit(self):
        self.args.update(exact=False,in_closure=False)
        self.assertEqual(self.result(),('R206 authenticated seed (not R207 fresh)',True))
    def test_changed_source_has_no_seed(self):
        self.args['exact']=False
        self.assertEqual(self.result(),('unchecked / invalidated',False))
    def test_legacy_is_not_checked(self):
        self.args.update(exact=False,baseline_status='legacy, not re-checked (standing classification)')
        self.assertEqual(self.result(),('legacy not applicable (not executed)',False))
    def test_preexisting_failure_is_not_fresh(self):
        self.args.update(exact=False,baseline_status='FAILED — pre-existing R137')
        self.assertEqual(self.result(),('pre-existing R137 failure (record only)',False))
    def test_old_negative_is_not_importable(self):
        self.args.update(exact=False,in_closure=False,seed_authenticated=False,
                         baseline_status='passed expected-negative contract')
        self.assertEqual(self.result(),('R206 expected-negative (not R207 fresh)',False))

    def test_inherited_negative_is_not_fresh(self):
        self.args.update(exact=False, in_closure=False, seed_authenticated=False,
                         baseline_status='fresh expected-negative PASS')
        self.assertEqual(self.result(), ('R206 expected-negative (not R207 fresh)', False))
    def test_inherited_failure_is_not_fresh(self):
        self.args.update(exact=False, in_closure=False, seed_authenticated=False,
                         baseline_status='fresh own-target FAILED')
        self.assertEqual(self.result(), ('R206 untrusted failure (record only)', False))
    def test_inherited_legacy_is_not_checked(self):
        self.args.update(exact=False, seed_authenticated=False,
                         baseline_status='legacy not applicable (not executed)')
        self.assertEqual(self.result(), ('legacy not applicable (not executed)', False))
    def test_inherited_preexisting_failure_is_not_checked(self):
        self.args.update(exact=False, seed_authenticated=False,
                         baseline_status='pre-existing R137 failure (record only)')
        self.assertEqual(self.result(), ('pre-existing R137 failure (record only)', False))

class DependencyRefreshContract(unittest.TestCase):
    def test_current_root_is_not_refreshed(self):
        self.assertFalse(needs_dependency_refresh({'end': '3'}, '2', {'parent': 'current'}, {'parent': 'current'}))
    def test_root_with_old_import_snapshot_is_refreshed(self):
        self.assertTrue(needs_dependency_refresh({'end': '3'}, '2', {'parent': 'old'}, {'parent': 'current'}))
    def test_root_before_transitive_source_epoch_is_refreshed(self):
        self.assertTrue(needs_dependency_refresh({'end': '1'}, '2', {'parent': 'current'}, {'parent': 'current'}))
    def test_missing_dependency_snapshot_is_refreshed(self):
        self.assertTrue(needs_dependency_refresh({'end': '3'}, '2', {}, {'parent': 'current'}))

if __name__=='__main__': unittest.main()
