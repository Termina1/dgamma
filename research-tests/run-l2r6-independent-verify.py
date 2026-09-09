#!/usr/bin/env python3
"""Compiler-free independent reconstruction, adapted from L2R5 verifier.
Reads this worktree/git objects and archived/raw records only. It never enters
another worktree, reads shared lock/window state, invokes a compiler or stages.
Not an independent human mathematical proof review; that gate stays required.
"""
import ast, datetime, hashlib, json, pathlib, re, subprocess, sys, tarfile
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=pathlib.Path('/tmp/dgamma-l2r6')
BASE='c09c0da2'
assert sys.argv[1:] in ([], ['--prepublication'])
prepublication=bool(sys.argv[1:])
OWNED='research-tests/O6-L2R6-Sources/'
DOC_EXCEPTIONS={'research-tests/O6-L2R5-CP3-DIFF-DRAFT.md','research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json','research-tests/run-l2r5-draft.py'}
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
def sha(data): return hashlib.sha256(data).hexdigest()
def declarations(data):
 text=data.decode();return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
def code(data): return '\n'.join(line for line in data.decode().splitlines() if not line.lstrip().startswith(('|||','--')))
def building(record,path):
 return re.search(r'^\d+/\d+: Building DGamma\.'+re.escape(pathlib.Path(path).stem)+r' \((?:'+re.escape(str(ROOT))+r'/)?'+re.escape(path)+r'\)$',record['transcript'],re.M)
assert pathlib.Path.cwd()==ROOT
assert git('branch','--show-current').decode().strip()=='cp5-thm73-lane-a8a10'
subprocess.run(['git','merge-base','--is-ancestor',BASE,'HEAD'],cwd=ROOT,check=True)
records=[json.loads(line) for line in (OUT/'ledger.jsonl').read_text().splitlines()]
byunit={r['unit']:r for r in records};assert len(byunit)==len(records)
receipts=[json.loads(line) for line in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
bycommit={r['resultingCommitHash']:r for r in receipts};assert len(bycommit)==len(receipts)
correction=json.loads((OUT/'target-correction.json').read_text())
repair=json.loads((ROOT/'research-tests/O6-L2R6-COMMENT-REPAIR.json').read_text())
for r in records:
 assert json.loads((OUT/(r['unit']+'.json')).read_text())==r
 assert (OUT/(r['unit']+'.log')).read_text()==r['transcript']
 assert sha((OUT/(r['unit']+'.source')).read_bytes())==r['sourceSHA256']
 assert r['path'].startswith(OWNED) or (r['unit']=='V0' and r['path']=='research-tests/O6-L2R5-Sources/DGamma/L2R5RootCatalog.idr')
 assert r['command'][-2:]==['--check',str(ROOT/r['path'])]
 assert all('/Work/dgamma/' not in part for part in r['command'])
 assert r['targetMtimeTouch']['path']==str(ROOT/r['path'])
 assert r['targetMtimeTouch']['newMtimeNs']>=r['targetMtimeTouch']['oldMtimeNs']
 assert r['fresh']==bool(building(r,r['path']))
 assert r['maxSampleRSSKiB']<19*1024*1024 and not r['heavyLockAcquired'] and r['heavyLockEvents']==[]
 if r['passed']:
  assert r['fresh'] and not r['interrupted'] and not r['sourceMutationObserved'] and r['exit']==0
  assert not r['expectedDiagnostic'] and 'Error:' not in r['transcript']
 if r.get('bundleSources'):
  assert r['unit'].startswith('D9-') and r['path']==OWNED+'DGamma/L2R6Phase.idr'
  assert {x['path'] for x in r['bundleSources']}=={OWNED+'DGamma/L2R6Anchors.idr',OWNED+'DGamma/L2R6PlacementFixtures.idr'}
  assert r['bundleFresh']==all(bool(building(r,x['path'])) for x in r['bundleSources'])
  for x in r['bundleSources']:
   assert sha((OUT/x['sourceFile']).read_bytes())==x['sourceSHA256']
   assert x['targetMtimeTouch']['path']==str(ROOT/x['path'])
for first,second in zip(records,records[1:]): assert first['end']<=second['start']
assert json.loads((OUT/'protocol-incidents.json').read_text())==[]
allcommits=git('log','--format=%H',BASE+'..HEAD').decode().splitlines()
assert set(allcommits)==set(bycommit), 'Every commit needs exactly one guarded receipt'
sourcecommits=[];commentcommits=[]
for commit in allcommits:
 receipt=bycommit[commit];r=byunit[receipt['invocation']]
 assert r['passed'] and r['fresh'] and r['sourceSHA256']==receipt['sourceHash']
 assert sha(git('show',commit+':'+r['path']))==r['sourceSHA256']
 assert r['end']<=receipt['timestampUTC']
 assert not any(r['end']<other['start']<receipt['timestampUTC'] for other in records)
 changed=git('diff-tree','--no-commit-id','--name-only','-r',commit).decode().splitlines()
 assert set(changed)<=set(receipt['paths'])
 if receipt['event']=='GUARDED COMMIT':
  sourcecommits.append(commit)
  expected=[r['path']]+[x['path'] for x in r.get('bundleSources',[])]
  assert r['path'] in changed and set(changed)<=set(expected)
  old=subprocess.run(['git','show',commit+'^:'+r['path']],cwd=ROOT,capture_output=True).stdout
  new=git('show',commit+':'+r['path'])
  assert len(declarations(new)-declarations(old))==1
  for path,h in receipt['sourceHashes'].items(): assert sha(git('show',commit+':'+path))==h
  for x in r.get('bundleSources',[]):
   before=git('show',commit+'^:'+x['path']);after=git('show',commit+':'+x['path'])
   assert declarations(before)==declarations(after)
   if x['path'].endswith('L2R6Anchors.idr'):
    assert before.count(correction['old'].encode())==1
    assert after==before.replace(correction['old'].encode(),correction['new'].encode())
   else: assert before==after
 else:
  assert receipt['event']=='GUARDED ARTIFACT COMMIT'
  for path in changed: assert sha(git('show',commit+':'+path))==receipt['artifactHashes'][path]
  for qualified in receipt['authorizedCommentRepairs']:
   path=qualified['path'];assert path==repair['path']
   before=git('show',commit+'^:'+path);after=git('show',commit+':'+path)
   assert after==before.replace(repair['old'].encode(),repair['new'].encode())
   assert before.count(repair['old'].encode())==1 and code(before)==code(after)
   assert sha(before)==qualified['beforeSHA256'] and sha(after)==qualified['repairedSHA256']
   assert any(v['unit'].startswith('V') and v['path']==path and v['passed'] and v['fresh'] and v['sourceSHA256']==sha(after) and v['end']<=receipt['timestampUTC'] for v in records)
   commentcommits.append(commit)
planpath='research-tests/O6-L2R6-FINAL-VALIDATION-PLAN.json'
assert (OUT/'final-validation-plan.json').read_bytes()==(ROOT/planpath).read_bytes()
plan=json.loads((ROOT/planpath).read_text());assert len(plan)==11
assert len({p['path'] for p in plan})==len({p['unit'] for p in plan})==len(plan)
plancommits=git('log','--format=%H',BASE+'..HEAD','--',planpath).decode().splitlines();assert len(plancommits)==1
assert git('show',plancommits[0]+':'+planpath)==(ROOT/planpath).read_bytes()
assert bycommit[plancommits[0]]['timestampUTC']<=byunit[plan[0]['unit']]['start']
seen=set()
for item in plan:
 assert set(item['dependsOn'])<=seen;seen.add(item['path'])
 r=byunit[item['unit']]
 assert r['passed'] and r['fresh'] and r['path']==item['path']
 assert r['sourceSHA256']==item['sourceHash']==sha((ROOT/item['path']).read_bytes())
paths=git('diff','--name-only',BASE).decode().splitlines()
assert all(p in DOC_EXCEPTIONS or p.startswith(('research-tests/O6-L2R6-','research-tests/run-l2r6-')) for p in paths)
newdecls={}
for path in paths:
 if not path.endswith('.idr'):continue
 assert path.startswith(OWNED)
 assert subprocess.run(['git','show',BASE+':'+path],cwd=ROOT,capture_output=True).returncode!=0
 current=(ROOT/path).read_bytes()
 assert '%default total' in current.decode() and '%unbound_implicits off' in current.decode()
 assert not re.search(r'\b(believe_me|assert_total|postulate|assert_smaller|partial|with|let)\b|\?[A-Za-z_]',code(current))
 newdecls[path]=sorted(declarations(current));assert path in seen
assert sum(map(len,newdecls.values()))==len(sourcecommits)==50
origins=json.loads((OUT/'declaration-origins.json').read_text());assert len(origins)==50
for origin in origins:
 line=(ROOT/origin['path']).read_text().splitlines()[origin['line']-1]
 assert re.match(r'^(?:[01] |record |data )?'+re.escape(origin['declaration'])+r'\b',line)
 assert bycommit[origin['commit']]['invocation']==origin['check']

assert len(commentcommits)==(0 if prepublication else 1)
if prepublication:
 before=git('show','HEAD:'+repair['path']);after=(ROOT/repair['path']).read_bytes()
 assert after==before.replace(repair['old'].encode(),repair['new'].encode()) and code(before)==code(after)
for letter,cap in [('A',14),('B',14),('C',10),('D',12)]:
 attempts={}
 for r in records:
  match=re.fullmatch(letter+r'(\d+)-([1-3])',r['unit'])
  if match: attempts.setdefault(int(match[1]),[]).append(r)
 assert set(attempts)==set(range(1,cap+1))
 for group in attempts.values():
  assert len(group)<=3 and group[-1]['passed'] and sum(r['passed'] for r in group)==1
  assert [int(r['unit'].rsplit('-',1)[1]) for r in group]==list(range(1,len(group)+1))
ledger=json.loads((ROOT/'research-tests/O6-L2R6-COMPILER-LEDGER.json').read_text())
archive=ROOT/'research-tests/O6-L2R6-COMPILER-EVIDENCE.tar.gz'
assert ledger['recordCount']==len(records) and ledger['passedCount']==sum(r['passed'] for r in records)
assert ledger['evidenceArchiveSHA256']==sha(archive.read_bytes())
assert set(sourcecommits)<={r['resultingCommitHash'] for r in ledger['commitReceipts']}
with tarfile.open(archive,'r:gz') as tar:
 for r in records:
  for suffix in ['.json','.log','.source']:
   filename=r['unit']+suffix;assert tar.extractfile(OUT.name+'/'+filename).read()==(OUT/filename).read_bytes()
  for extra in r.get('bundleSources',[]): assert tar.extractfile(OUT.name+'/'+extra['sourceFile']).read()==(OUT/extra['sourceFile']).read_bytes()
 for filename in ['final-validation-plan.json','target-correction.json','comment-repair.json','shift.json']:
  assert tar.extractfile(OUT.name+'/'+filename).read()==(OUT/filename).read_bytes()
rehome=json.loads((ROOT/'research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json').read_text())
assert rehome['cp3Blob']==git('rev-parse','HEAD:src/DGamma/CP3.idr').decode().strip()
for path,h in rehome['checkedSourceSHA256'].items():assert sha((ROOT/path).read_bytes())==h
moved='\n'.join((ROOT/'src/DGamma/CP3.idr').read_text().splitlines()[2092:2120])+'\n';assert sha(moved.encode())==rehome['movedCombinedSHA256']
draft=(ROOT/'research-tests/O6-L2R5-CP3-DIFF-DRAFT.md').read_text()
for section in rehome['tier1Sections']:
 fragment=draft.split('### '+section['title']+'\n\n```idris\n',1)[1].split('```',1)[0];assert sha(fragment.encode())==section['sha256']
assert 'NOT YET SIGNABLE' in draft and 'PARTIALLY CHECKED' in draft and 'GeneralDistanceIteration' in draft
mapping={};tree=ast.parse((ROOT/'research-tests/run-l2r5-draft.py').read_text())
for node in tree.body:
 if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='mapping' for t in node.targets):mapping.update(ast.literal_eval(node.value))
 if isinstance(node,ast.For) and isinstance(node.target,ast.Tuple) and [ast.unparse(t) for t in node.target.elts]==['a','b']:mapping.update(dict(ast.literal_eval(node.iter)))
assert mapping==rehome['renamings'] and len(mapping)==30
assert not git('diff',BASE,'--','src/','research/','dgamma.ipkg','README.md','NOTES.md','THM73-PLAN.md')
assert not git('diff','--cached','--name-only')
if not prepublication:
 assert not git('diff','--name-only') and not git('ls-files','--others','--exclude-standard')
else:
 pending=git('diff','--name-only').decode().splitlines()+git('ls-files','--others','--exclude-standard').decode().splitlines()
 assert all(path==repair['path'] or (path.startswith(('research-tests/O6-L2R6-','research-tests/run-l2r6-')) and not path.endswith('.idr')) for path in pending)
processes=subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines())
shift=json.loads((OUT/'shift.json').read_text())
assert all(r['start']<shift['attemptCutoff'] for r in records if re.fullmatch(r'[ABCD]\d+-[1-3]',r['unit']))
assert all(byunit[p['unit']]['end']<shift['validationCutoff'] for p in plan)
report=dict(status='PREPUBLICATION_PASS' if prepublication else 'PASS',head=git('rev-parse','HEAD').decode().strip(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),invocationCount=len(records),passedCount=sum(r['passed'] for r in records),failedCount=sum(not r['passed'] for r in records),finalCheckCount=len(plan),newDeclarationCount=50,newDeclarations=newdecls,proofCommitCount=50,commentOnlyRepairCount=len(commentcommits),commentRepairValidatedPending=prepublication,allCommitsReceiptAuthenticated=True,allSourceHashesAndLogsAuthenticated=True,D9BodyOnlyBundleAndFixtureRecheckAuthenticated=True,immutableFinalPlanPublishedBeforeChecks=True,finalPlanLeafBeforeDependent=True,allFinalSourcesFreshlyChecked=True,allInvocationsSerialized=True,maxSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records),RSSQualification='250ms sampled, not continuous peak',archiveSHA256=sha(archive.read_bytes()),predecessorProofSourcesUntouched=True,authorizedPredecessorDocsOnly=sorted(DOC_EXCEPTIONS),tier1CodeHashesUnchanged=True,all30RenamingsSerialized=True,productionAndFrozenResearchUntouched=True,noSharedLockInteractionByCheckRunner=True,sharedLockAndWindowNotInspected=True,noOwnCompiler=True,noStagedFiles=True,cleanTrackedTree=not prepublication,noUntrackedDeliverables=not prepublication,independentHumanProofReviewRequired=True)
(OUT/('prepublication-verification.json' if prepublication else 'independent-verification.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='newDeclarations'},indent=2))
