#!/usr/bin/env python3
"""Compiler-free regression tests for the ACTUAL runner/verifier helper ASTs.
No compiler or commit guard is invoked, and no process is signalled. Isolated
helper functions are tested with fake ps output and adversarial freshness text.
"""
import ast, datetime, json, pathlib, re, types, unittest, tempfile
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r3')
assert pathlib.Path.cwd() == ROOT

def helper(path, name, globals_):
 tree = ast.parse((ROOT/path).read_text())
 node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name)
 scope = dict(globals_)
 exec(compile(ast.Module(body=[node], type_ignores=[]), path, 'exec'), scope)
 return scope[name]

class EvidenceTests(unittest.TestCase):
 def setUp(self):
  self.declarations = helper('research-tests/run-l2r3-check.py', 'declarations', {'re': re})
  self.building = helper('research-tests/run-l2r3-independent-verify.py', 'building', {'re': re, 'pathlib': pathlib, 'ROOT': ROOT})
 def test_one_new_top_level_declaration(self):
  old = b'0 oldProof : Unit\noldProof = ()\n'
  new = old + b'record Package where\n  constructor MkPackage\n  0 field : Unit\n'
  self.assertEqual(self.declarations(new)-self.declarations(old), {'Package'})
 def test_two_new_declarations_are_distinct(self):
  self.assertEqual(len(self.declarations(b'0 one : Unit\nrecord Two where\n  constructor MkTwo\n')), 2)
 def test_body_only_companion_has_no_new_declaration(self):
  self.assertEqual(self.declarations(b'f : Nat -> Nat\nf x = x\n'), self.declarations(b'f : Nat -> Nat\nf x = S x\n'))
 def test_own_building_line_required(self):
  path = 'research-tests/O6-L2R3-Sources/DGamma/L2R3RootPhase.idr'
  self.assertTrue(self.building({'transcript': '1/1: Building DGamma.L2R3RootPhase ('+str(ROOT/path)+')\n'}, path))
  self.assertFalse(self.building({'transcript': ''}, path))
  self.assertFalse(self.building({'transcript': 'Already checked; cached\n'}, path))
 def test_dependency_or_wrong_worktree_not_freshness(self):
  path = 'research-tests/O6-L2R3-Sources/DGamma/L2R3RootPhase.idr'
  self.assertFalse(self.building({'transcript': '1/1: Building DGamma.L2R3SmallStates ('+str(ROOT/'research-tests/O6-L2R3-Sources/DGamma/L2R3SmallStates.idr')+')\n'}, path))
  self.assertFalse(self.building({'transcript': '1/1: Building DGamma.L2R3RootPhase (/Users/vyacheslavshebanov/Work/dgamma/'+path+')\n'}, path))
 def test_classifier_does_not_own_main_or_wrapper(self):
  engine = '/opt/homebrew/opt/chezscheme/bin/chez --program /opt/homebrew/libexec/bin/idris2_app/idris2.so'
  rows = '\n'.join([
   '101 1 500 '+engine+' --source-dir '+str(ROOT/'src')+' --check '+str(ROOT/'research-tests/O6-L2R3-Sources/DGamma/L2R3RootPhase.idr'),
   '102 1 999999 '+engine+' --source-dir /Users/vyacheslavshebanov/Work/dgamma/src --check /Users/vyacheslavshebanov/Work/dgamma/research/DGamma/CP5ConfluenceLocalDiamondSpike.idr',
   '103 1 100 /usr/bin/python3 -I wrapper.py '+engine+' '+str(ROOT/'src'),
   '104 1 200 '+engine+' --source-dir /elsewhere/src --check /elsewhere/Test.idr'])
  fake = types.SimpleNamespace(check_output=lambda *args, **kwargs: rows)
  scan = helper('research-tests/run-l2r3-check.py', 'compiler_processes', {'pathlib': pathlib, 'subprocess': fake, 'ROOT': ROOT})
  result = {p['pid']: p for p in scan()}
  self.assertEqual(set(result), {101, 102, 104})
  self.assertEqual(result[101]['classification'], 'lane2')
  self.assertEqual(result[102]['classification'], 'main-lane compiler (separate worktree)')
  self.assertIn('never killed', result[104]['classification'])
 def assert_expression(self, text, scope):
  tree = ast.parse((ROOT/'research-tests/run-l2r3-check.py').read_text())
  node = next(n for n in ast.walk(tree) if isinstance(n, ast.Assert) and text in ast.unparse(n.test))
  return eval(compile(ast.Expression(node.test), '<actual runner assertion>', 'eval'), scope)
 def test_target_guard_rejects_missing_empty_and_outside(self):
  with tempfile.TemporaryDirectory(prefix='dgamma-l2r3-test-') as folder:
   root = pathlib.Path(folder).resolve()
   target = root/'source.idr'
   scope = {'target':target, 'ROOT':root}
   self.assertFalse(self.assert_expression('target.is_file()', scope))
   target.write_text('')
   self.assertFalse(self.assert_expression('target.is_file()', scope))
   target.write_text('module Fixture\n')
   self.assertTrue(self.assert_expression('target.is_file()', scope))
   self.assertFalse(self.assert_expression('target.is_file()', {'target':target, 'ROOT':root/'other'}))
 def test_actual_caps_no_self_extension(self):
  for unit, expected in [('A24-1',True),('A25-1',False),('B12-1',True),('B13-1',False),('C14-1',True),('C15-1',False)]:
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
 def test_all_runner_files_parse_without_execution(self):
  for path in sorted((ROOT/'research-tests').glob('run-l2r3-*.py')):
   compile(path.read_bytes(), str(path), 'exec')

suite = unittest.defaultTestLoader.loadTestsFromTestCase(EvidenceTests)
result = unittest.TextTestRunner(verbosity=2).run(suite)
report = dict(status='PASS' if result.wasSuccessful() else 'FAIL', testsRun=result.testsRun, failures=len(result.failures), errors=len(result.errors), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), compilerInvoked=False, processesSignalled=False, mainWorktreeAccessed=False)
(OUT/'evidence-tests.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
raise SystemExit(0 if result.wasSuccessful() else 1)
