#!/usr/bin/env python3
"""Adapted from run-l2r7-evidence-tests.py: compiler-free guard AST tests.
Executes only selected pure helper/assertion expressions, never the checker,
launcher or commit module top levels. No compiler, commit or source writes.
"""
import ast,json,pathlib,re,tempfile,types,unittest
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=pathlib.Path('/tmp/dgamma-l2r9')
assert pathlib.Path.cwd()==ROOT
source=(ROOT/'research-tests/run-l2r9-check.py').read_text();tree=ast.parse(source)
def expr(node,env):return eval(compile(ast.Expression(node),'<actual-guard-AST>','eval'),env)
def assertion(fragment):
 found=[n.test for n in ast.walk(tree) if isinstance(n,ast.Assert) and fragment in ast.get_source_segment(source,n)]
 assert len(found)==1,(fragment,len(found));return found[0]
def helper(name,env):
 node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name==name)
 exec(compile(ast.Module(body=[node],type_ignores=[]),'<actual-helper-AST>','exec'),env);return env[name]
class Guards(unittest.TestCase):
 def test_bounded_ids(self):
  a=assertion('Bounded attempt or validation ID')
  for u in ['A1-1','B14-3','C8-2','D10-1','V21']:self.assertTrue(expr(a,{'re':re,'unit':u}))
  for u in ['A1-4','A0-1','E1-1','package','D10']:self.assertFalse(expr(a,{'re':re,'unit':u}))
 def test_unit_caps(self):
  a=assertion("<= {'A':16")
  for letter,cap in {'A':16,'B':12,'C':14,'D':14}.items():
   self.assertTrue(expr(a,{'unit':f'{letter}{cap}-1'}));self.assertFalse(expr(a,{'unit':f'{letter}{cap+1}-1'}))
 def test_target_ownership(self):
  a=assertion('Lane-owned targets or exact unchanged bootstrap')
  for p,u,ok in [('research-tests/O6-L2R9-Sources/DGamma/X.idr','A1-1',True),('src/DGamma/CP3.idr','A1-1',False),('research-tests/O6-L2R8-Sources/DGamma/L2R8ReleaseScan.idr','V0',True),('research-tests/O6-L2R8-Sources/DGamma/L2R8ReleaseScan.idr','V1',False)]:self.assertEqual(expr(a,{'path':p,'unit':u,'commentTarget':False}),ok)
 def test_no_package(self):self.assertFalse(expr(assertion('Whole package and cold rebuild'),{'path':'package'}))
 def test_attempt_count(self):
  a=assertion("sum(r['unit']")
  for n in range(4):self.assertEqual(expr(a,{'previous':[{'unit':f'A1-{i+1}'} for i in range(n)],'unit':'A1-3'}),n<3)
 def test_no_retry_after_pass(self):
  a=assertion("not any(r['passed']")
  self.assertFalse(expr(a,{'previous':[{'unit':'B1-1','passed':True}],'unit':'B1-2'}))
 def test_source_closed(self):
  a=assertion('Source phase closed')
  with tempfile.TemporaryDirectory(dir=OUT) as d:
   p=pathlib.Path(d);self.assertTrue(expr(a,{'OUT':p}));(p/'source-closed.json').write_text('{}');self.assertFalse(expr(a,{'OUT':p}))
 def test_declaration_detector(self):
  f=helper('declarations',{'re':re});self.assertEqual(f(b'public export\n0 proof : Type\nrecord Box where\n  field : Nat\n'),{'proof','Box'})
 def test_mutation_monitor(self):
  f=helper('sources_unchanged',{})
  with tempfile.TemporaryDirectory(dir=OUT) as d:
   p=pathlib.Path(d)/'a';p.write_bytes(b'x');self.assertTrue(f(p,b'x',[]));p.write_bytes(b'y');self.assertFalse(f(p,b'x',[]));p.unlink();self.assertFalse(f(p,b'x',[]))
 def test_building_and_pass(self):
  a=next(n.value for n in ast.walk(tree) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='passed' for t in n.targets))
  base={'fresh':True,'buildingLines':['own'],'bundle_fresh':True,'interrupted':False,'process':types.SimpleNamespace(returncode=0),'text':'own Building','diagnostic':None,'symbol':None}
  self.assertTrue(expr(a,dict(base)))
  for change in [{'fresh':False},{'buildingLines':[]},{'buildingLines':['own','extra']},{'interrupted':True},{'process':types.SimpleNamespace(returncode=1)},{'text':'Error: fake'}]:self.assertFalse(expr(a,{**base,**change}))
 def test_compiler_ownership(self):
  rows=f'1 0 99 /opt/chez --program /x/idris2_app/idris2.so --check {ROOT}/x.idr\n2 0 99 /opt/chez --program /x/idris2_app/idris2.so --check /Users/vyacheslavshebanov/Work/dgamma/x.idr\n3 0 99 /opt/chez --program /x/idris2_app/idris2.so --check /tmp/unknown.idr\n4 0 99 /bin/echo /x/idris2_app/idris2.so {ROOT}/x\n'
  f=helper('compiler_processes',{'ROOT':ROOT,'pathlib':pathlib,'subprocess':types.SimpleNamespace(check_output=lambda *a,**k:rows)})
  got=f();self.assertEqual([x['pid'] for x in got],[1,2,3]);self.assertEqual(got[0]['classification'],'lane2');self.assertNotEqual(got[1]['classification'],'lane2');self.assertNotEqual(got[2]['classification'],'lane2')
 def test_source_commit_no_validation_bypass(self):
  s=(ROOT/'research-tests/run-l2r9-commit.py').read_text();self.assertIn("assert not unit.startswith('V')",s);self.assertIn("record['buildingCount'] == 1",s)
 def test_no_companion_authority(self):
  self.assertIn('bundle=[]',source);s=(ROOT/'research-tests/run-l2r9-commit.py').read_text();self.assertIn("assert not record.get('bundleSources')",s)
 def test_caps_and_closure_files(self):
  d=json.loads((OUT/'source-closed.json').read_text());self.assertTrue(d['noFurtherProofAttempts']);self.assertEqual(d['caps'],{'A':16,'B':12,'C':14,'D':14,'E':3})
 def test_all_runner_python_parses(self):
  for p in ROOT.glob('research-tests/run-l2r9-*.py'):ast.parse(p.read_text(),filename=str(p))
 def test_final_plan_unique_owned(self):
  plan=json.loads((OUT/'final-validation-plan.json').read_text());self.assertEqual(len(plan),17);self.assertEqual(len({r['unit'] for r in plan}),17)
  self.assertTrue(all(r['path'].startswith('research-tests/O6-L2R9-Sources/') for r in plan))
 def test_comment_target_exact(self):
  repair=json.loads((ROOT/'research-tests/O6-L2R9-COMMENT-REPAIR.json').read_text())
  f=helper('comment_target_allowed',{'re':re})
  self.assertTrue(f('V5',repair['path'],repair['afterSHA256'],repair))
  for unit,path,digest in [('A1-1',repair['path'],repair['afterSHA256']),('V5','src/DGamma/CP3.idr',repair['afterSHA256']),('V5',repair['path'],repair['beforeSHA256']),('Vbad',repair['path'],repair['afterSHA256'])]:self.assertFalse(f(unit,path,digest,repair))
 def test_comment_authority_frozen_digest(self):
  import hashlib
  actual=hashlib.sha256((ROOT/'research-tests/O6-L2R9-COMMENT-REPAIR.json').read_bytes()).hexdigest()
  for path in ['research-tests/run-l2r9-check.py','research-tests/run-l2r9-artifact-commit.py']:
   t=ast.parse((ROOT/path).read_text());value=next(n.value.value for n in t.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='AUTHORITY_SHA256' for x in n.targets));self.assertEqual(value,actual)
 def test_actual_comment_patch_assertion_rejects_extra_bytes(self):
  repair=json.loads((ROOT/'research-tests/O6-L2R9-COMMENT-REPAIR.json').read_text());after=(ROOT/repair['path']).read_bytes();before=after.replace(repair['new'].encode(),repair['old'].encode())
  src=(ROOT/'research-tests/run-l2r9-artifact-commit.py').read_text();t=ast.parse(src);a=next(n.test for n in ast.walk(t) if isinstance(n,ast.Assert) and 'before.count(old)' in ast.get_source_segment(src,n))
  class MemoryRoot:
   def __init__(self,data):self.data=data
   def __truediv__(self,path):return types.SimpleNamespace(read_bytes=lambda:self.data)
  env={'before':before,'old':repair['old'].encode(),'new':repair['new'].encode(),'path':repair['path'],'ROOT':MemoryRoot(after)}
  self.assertTrue(expr(a,env));self.assertFalse(expr(a,{**env,'ROOT':MemoryRoot(after+b'extra body change')}))
 def test_repl_is_only_diagnostic(self):
  d=json.loads((OUT/'A14-diagnostic.json').read_text());self.assertEqual(d['exit'],0);self.assertFalse(d['sourceMutationObserved']);self.assertFalse(d['targetTouch']);self.assertEqual(d['scratchFiles'],[]);self.assertEqual(d['transcript'].count('> [3]'),2)
  self.assertIn('not proof/validation',d['kind']);self.assertNotIn('passed',d)
if __name__=='__main__':unittest.main(verbosity=2)
