#!/usr/bin/env python3
"""Compiler-free regression tests for the ACTUAL runner/verifier helper ASTs.
No compiler or commit guard is invoked, and no process is signalled. Isolated
helper functions are tested with fake ps output and adversarial freshness text.
"""
import ast, datetime, json, pathlib, re, types, unittest, tempfile
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r7')
assert pathlib.Path.cwd() == ROOT

def helper(path, name, globals_):
 tree = ast.parse((ROOT/path).read_text())
 node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name)
 scope = dict(globals_)
 exec(compile(ast.Module(body=[node], type_ignores=[]), path, 'exec'), scope)
 return scope[name]

class EvidenceTests(unittest.TestCase):
 def setUp(self):
  self.declarations = helper('research-tests/run-l2r7-check.py', 'declarations', {'re': re})
  self.building = helper('research-tests/run-l2r7-independent-verify.py', 'building', {'re': re, 'pathlib': pathlib, 'ROOT': ROOT})
 def test_one_new_top_level_declaration(self):
  old = b'0 oldProof : Unit\noldProof = ()\n'
  new = old + b'record Package where\n  constructor MkPackage\n  0 field : Unit\n'
  self.assertEqual(self.declarations(new)-self.declarations(old), {'Package'})
 def test_two_new_declarations_are_distinct(self):
  self.assertEqual(len(self.declarations(b'0 one : Unit\nrecord Two where\n  constructor MkTwo\n')), 2)
 def test_body_only_companion_has_no_new_declaration(self):
  self.assertEqual(self.declarations(b'f : Nat -> Nat\nf x = x\n'), self.declarations(b'f : Nat -> Nat\nf x = S x\n'))
 def test_own_building_line_required(self):
  path = 'research-tests/O6-L2R7-Sources/DGamma/L2R7RootPhase.idr'
  self.assertTrue(self.building({'transcript': '1/1: Building DGamma.L2R7RootPhase ('+str(ROOT/path)+')\n'}, path))
  self.assertFalse(self.building({'transcript': ''}, path))
  self.assertFalse(self.building({'transcript': 'Already checked; cached\n'}, path))
 def test_dependency_or_wrong_worktree_not_freshness(self):
  path = 'research-tests/O6-L2R7-Sources/DGamma/L2R7RootPhase.idr'
  self.assertFalse(self.building({'transcript': '1/1: Building DGamma.L2R7SmallStates ('+str(ROOT/'research-tests/O6-L2R7-Sources/DGamma/L2R7SmallStates.idr')+')\n'}, path))
  self.assertFalse(self.building({'transcript': '1/1: Building DGamma.L2R7RootPhase (/Users/vyacheslavshebanov/Work/dgamma/'+path+')\n'}, path))
 def test_classifier_does_not_own_main_or_wrapper(self):
  engine = '/opt/homebrew/opt/chezscheme/bin/chez --program /opt/homebrew/libexec/bin/idris2_app/idris2.so'
  rows = '\n'.join([
   '101 1 500 '+engine+' --source-dir '+str(ROOT/'src')+' --check '+str(ROOT/'research-tests/O6-L2R7-Sources/DGamma/L2R7RootPhase.idr'),
   '102 1 999999 '+engine+' --source-dir /Users/vyacheslavshebanov/Work/dgamma/src --check /Users/vyacheslavshebanov/Work/dgamma/research/DGamma/CP5ConfluenceLocalDiamondSpike.idr',
   '103 1 100 /usr/bin/python3 -I wrapper.py '+engine+' '+str(ROOT/'src'),
   '104 1 200 '+engine+' --source-dir /elsewhere/src --check /elsewhere/Test.idr'])
  fake = types.SimpleNamespace(check_output=lambda *args, **kwargs: rows)
  scan = helper('research-tests/run-l2r7-check.py', 'compiler_processes', {'pathlib': pathlib, 'subprocess': fake, 'ROOT': ROOT})
  result = {p['pid']: p for p in scan()}
  self.assertEqual(set(result), {101, 102, 104})
  self.assertEqual(result[101]['classification'], 'lane2')
  self.assertEqual(result[102]['classification'], 'main-lane compiler (separate worktree)')
  self.assertIn('never killed', result[104]['classification'])
 def assert_expression(self, text, scope):
  tree = ast.parse((ROOT/'research-tests/run-l2r7-check.py').read_text())
  node = next(n for n in ast.walk(tree) if isinstance(n, ast.Assert) and text in ast.unparse(n.test))
  return eval(compile(ast.Expression(node.test), '<actual runner assertion>', 'eval'), scope)
 def test_target_guard_rejects_missing_empty_and_outside(self):
  with tempfile.TemporaryDirectory(prefix='dgamma-l2r7-test-') as folder:
   root = pathlib.Path(folder).resolve()
   target = root/'source.idr'
   scope = {'target':target, 'ROOT':root}
   self.assertFalse(self.assert_expression('target.is_file()', scope))
   target.write_text('')
   self.assertFalse(self.assert_expression('target.is_file()', scope))
   target.write_text('module Fixture\n')
   self.assertTrue(self.assert_expression('target.is_file()', scope))
   self.assertFalse(self.assert_expression('target.is_file()', {'target':target, 'ROOT':root/'other'}))
 def test_exact_bootstrap_exception_not_predecessor_authority(self):
  old='research-tests/O6-L2R6-Sources/DGamma/L2R6ForcedScan.idr'
  for unit,path,ok in [('V0',old,True),('V1',old,False),('A1-1',old,False),('V0','research-tests/O6-L2R4-Sources/DGamma/Other.idr',False),('A1-1','research-tests/O6-L2R7-Sources/DGamma/Owned.idr',True)]:
   self.assertEqual(self.assert_expression("path.startswith('research-tests/O6-L2R7-Sources/')",{'unit':unit,'path':path}),ok)
 def test_actual_caps_no_self_extension(self):
  for unit, expected in [('A22-1',True),('A23-1',False),('B16-1',True),('B17-1',False),('C12-1',True),('C13-1',False),('D8-1',True),('D9-1',False)]:
   self.assertEqual(self.assert_expression('int(unit.split', {'unit':unit}), expected)
 def test_actual_attempt_identifiers_bounded(self):
  for unit, expected in [('A1-3',True),('A1-4',False),('B0-1',False),('A-1',False),('V00',True),('V12',True),('freeform',False)]:
   self.assertEqual(bool(self.assert_expression('re.fullmatch', {'unit':unit,'re':re})), expected)
 def test_attempt_budget_and_no_retry_after_pass(self):
  scope = {'unit':'A1-3','previous':[{'unit':'A1-1','passed':False},{'unit':'A1-2','passed':False}]}
  self.assertTrue(self.assert_expression('sum(',scope))
  scope['previous'].append({'unit':'A1-3','passed':False})
  self.assertFalse(self.assert_expression('sum(',scope))
  scope['previous']=[{'unit':'A1-1','passed':True}]
  self.assertFalse(self.assert_expression("r['passed']",scope))
 def actual_pass_expression(self, **updates):
  tree=ast.parse((ROOT/'research-tests/run-l2r7-check.py').read_text())
  node=next(n for n in ast.walk(tree) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='passed' for t in n.targets))
  scope=dict(fresh=True,bundle_fresh=True,interrupted=False,process=types.SimpleNamespace(returncode=0),text='1/1: Building Target',diagnostic=None,symbol=None)
  scope.update(updates)
  return eval(compile(ast.Expression(node.value),'<actual PASS guard>','eval'),scope)
 def test_error_exit_zero_is_not_pass(self):
  self.assertTrue(self.actual_pass_expression())
  self.assertFalse(self.actual_pass_expression(text='Error: undefined name',process=types.SimpleNamespace(returncode=0)))
 def test_interrupted_or_cached_or_nonzero_is_not_pass(self):
  self.assertFalse(self.actual_pass_expression(interrupted=True))
  self.assertFalse(self.actual_pass_expression(fresh=False))
  self.assertFalse(self.actual_pass_expression(process=types.SimpleNamespace(returncode=1)))
 def test_default_bundle_empty(self):
  tree=ast.parse((ROOT/'research-tests/run-l2r7-check.py').read_text())
  node=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='bundle' for t in n.targets))
  self.assertEqual(ast.literal_eval(node.value),[])
 def test_runtime_mutation_guard_handles_missing_and_changed_target(self):
  unchanged=helper('research-tests/run-l2r7-check.py','sources_unchanged',{})
  with tempfile.TemporaryDirectory(prefix='l2r7-mutation-test-') as folder:
   path=pathlib.Path(folder)/'target.idr';other=pathlib.Path(folder)/'companion.idr'
   path.write_bytes(b'original');other.write_bytes(b'companion')
   self.assertTrue(unchanged(path,b'original',[(other,b'companion')]))
   path.write_bytes(b'changed');self.assertFalse(unchanged(path,b'original',[]))
   path.unlink();self.assertFalse(unchanged(path,b'original',[]))
   path.write_bytes(b'original');other.unlink();self.assertFalse(unchanged(path,b'original',[(other,b'companion')]))
 def test_shared_lock_and_window_never_accessed(self):
  for path in ['research-tests/run-l2r7-check.py','research-tests/run-l2r7-independent-verify.py','research-tests/run-l2r7-archive.py']:
   source=(ROOT/path).read_text()
   self.assertNotIn("Path('/tmp/dgamma-heavy.lock",source)
   self.assertNotIn('LOCK.',source)
   self.assertNotIn('dgamma-rebuild-window.json',source)
 def test_no_companion_authority(self):
  source=(ROOT/'research-tests/run-l2r7-check.py').read_text()
  self.assertNotIn("if unit.startswith('D9-'):",source)
  tree=ast.parse((ROOT/'research-tests/run-l2r7-commit.py').read_text())
  node=next(n for n in ast.walk(tree) if isinstance(n,ast.Assert) and ast.unparse(n.test)=="not record.get('bundleSources')")
  expr=compile(ast.Expression(node.test),'<actual no-companion guard>','eval')
  self.assertTrue(eval(expr,{'record':{'bundleSources':[]}}))
  self.assertFalse(eval(expr,{'record':{'bundleSources':[{'path':'pretend'}]}}))
 def test_header_repairs_are_exact_and_ast_preserving(self):
  import subprocess
  for repair in json.loads((ROOT/'research-tests/O6-L2R7-HEADER-REPAIRS.json').read_text()):
   before=subprocess.check_output(['git','show','87e9fb20:'+repair['path']],cwd=ROOT)
   after=(ROOT/repair['path']).read_bytes()
   self.assertEqual(after,before.replace(repair['old'].encode(),repair['new'].encode()))
   old_tree,new_tree=ast.parse(before),ast.parse(after)
   old_tree.body=old_tree.body[1:];new_tree.body=new_tree.body[1:]
   self.assertEqual(ast.dump(old_tree),ast.dump(new_tree))
 def test_v1_whitespace_has_no_proof_delta(self):
  self.assertEqual((OUT/'B2-1.source').read_bytes().rstrip()+b'\n',(OUT/'V1.source').read_bytes())
  self.assertTrue(json.loads((OUT/'V1.json').read_text())['passed'])
 def test_validation_cannot_bypass_source_caps(self):
  tree=ast.parse((ROOT/'research-tests/run-l2r7-commit.py').read_text())
  node=next(n for n in ast.walk(tree) if isinstance(n,ast.Assert) and ast.unparse(n.test)=="unit == 'V1'")
  expr=compile(ast.Expression(node.test),'<actual validation publication restriction>','eval')
  self.assertTrue(eval(expr,{'unit':'V1'}));self.assertFalse(eval(expr,{'unit':'V10'}))
 def test_a8_stop_reverted_and_not_restated(self):
  stop=json.loads((OUT/'A8-stop.json').read_text())
  self.assertFalse(stop['retained']);self.assertEqual(stop['attempts'],3)
  for p in (ROOT/'research-tests/O6-L2R7-Sources/DGamma').glob('*.idr'):
   self.assertNotIn('elemDecConsObserved',self.declarations(p.read_bytes()))
 def test_plan_hashes_and_direct_dependency_order(self):
  import hashlib
  plan=json.loads((ROOT/'research-tests/O6-L2R7-FINAL-VALIDATION-PLAN.json').read_text())
  self.assertEqual(len(plan),17);seen=set()
  for item in plan:
   self.assertTrue(set(item['dependsOn'])<=seen);seen.add(item['path'])
   self.assertEqual(item['sourceHash'],hashlib.sha256((ROOT/item['path']).read_bytes()).hexdigest())
 def test_artifact_guard_has_no_idris_repair_authority(self):
  tree=ast.parse((ROOT/'research-tests/run-l2r7-artifact-commit.py').read_text())
  node=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='REPAIRS' for t in n.targets))
  self.assertEqual(ast.literal_eval(node.value),{})
 def test_manifest_has_all_generator_renamings(self):
  tree=ast.parse((ROOT/'research-tests/run-l2r5-draft.py').read_text())
  mapping=ast.literal_eval(next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='mapping' for t in n.targets)))
  for node in tree.body:
   if isinstance(node,ast.For) and isinstance(node.target,ast.Tuple) and [ast.unparse(t) for t in node.target.elts]==['a','b']:
    mapping.update(dict(ast.literal_eval(node.iter)))
  self.assertEqual(mapping,json.loads((ROOT/'research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json').read_text())['renamings'])
 def test_all_runner_files_parse_without_execution(self):
  for path in sorted((ROOT/'research-tests').glob('run-l2r7-*.py')):
   compile(path.read_bytes(), str(path), 'exec')

suite = unittest.defaultTestLoader.loadTestsFromTestCase(EvidenceTests)
result = unittest.TextTestRunner(verbosity=2).run(suite)
report = dict(status='PASS' if result.wasSuccessful() else 'FAIL', testsRun=result.testsRun, failures=len(result.failures), errors=len(result.errors), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), compilerInvoked=False, processesSignalled=False, mainWorktreeAccessed=False)
(OUT/'evidence-tests.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
raise SystemExit(0 if result.wasSuccessful() else 1)
