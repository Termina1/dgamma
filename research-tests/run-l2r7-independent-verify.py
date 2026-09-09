#!/usr/bin/env python3
"""Compiler-free independent reconstruction, adapted from L2R6 verifier.
Reads lane2/git objects and raw/archive records only. No compiler, staging,
shared lock/window inspection or main-worktree IO. Not human proof review.
"""
import ast, datetime, hashlib, json, pathlib, re, subprocess, sys, tarfile
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=pathlib.Path('/tmp/dgamma-l2r7');BASE='87e9fb20';OWNED='research-tests/O6-L2R7-Sources/'
DOC_EXCEPTIONS={'research-tests/O6-L2R5-CP3-DIFF-DRAFT.md','research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json','research-tests/run-l2r6-check.py','research-tests/run-l2r6-commit.py','research-tests/run-l2r6-artifact-commit.py'}
assert sys.argv[1:] in ([],['--prepublication'])
prepublication=bool(sys.argv[1:])
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
for r in records:
 assert json.loads((OUT/(r['unit']+'.json')).read_text())==r
 assert (OUT/(r['unit']+'.log')).read_text()==r['transcript']
 assert sha((OUT/(r['unit']+'.source')).read_bytes())==r['sourceSHA256']
 assert r['path'].startswith(OWNED) or (r['unit']=='V0' and r['path']=='research-tests/O6-L2R6-Sources/DGamma/L2R6ForcedScan.idr')
 assert r['command'][-2:]==['--check',str(ROOT/r['path'])]
 assert all('/Work/dgamma/' not in part for part in r['command'])
 assert not r.get('bundleSources') and r['bundleFresh']
 assert r['targetMtimeTouch']['path']==str(ROOT/r['path'])
 assert r['targetMtimeTouch']['newMtimeNs']>=r['targetMtimeTouch']['oldMtimeNs']
 assert r['fresh']==bool(building(r,r['path']))
 assert r['maxSampleRSSKiB']<19*1024*1024 and not r['heavyLockAcquired'] and r['heavyLockEvents']==[]
 assert not r['sourceMutationObserved']
 if r['passed']:
  assert r['fresh'] and not r['interrupted'] and r['exit']==0 and not r['expectedDiagnostic'] and 'Error:' not in r['transcript']
for first,second in zip(records,records[1:]):assert first['end']<=second['start']
allcommits=git('log','--format=%H',BASE+'..HEAD').decode().splitlines()
assert set(allcommits)==set(bycommit),'Every commit needs exactly one guarded receipt'
sourcecommits=[]
for commit in allcommits:
 receipt=bycommit[commit];r=byunit[receipt['invocation']]
 assert r['passed'] and r['fresh'] and r['sourceSHA256']==receipt['sourceHash']
 assert sha(git('show',commit+':'+r['path']))==r['sourceSHA256']
 assert r['end']<=receipt['timestampUTC']
 assert not any(r['end']<other['start']<receipt['timestampUTC'] for other in records)
 changed=git('diff-tree','--no-commit-id','--name-only','-r',commit).decode().splitlines()
 assert set(changed)<=set(receipt['paths'])
 if receipt['event']=='GUARDED COMMIT':
  sourcecommits.append(commit);assert changed==[r['path']] and r['path'].startswith(OWNED)
  old=subprocess.run(['git','show',commit+'^:'+r['path']],cwd=ROOT,capture_output=True).stdout
  new=git('show',commit+':'+r['path']);assert len(declarations(new)-declarations(old))==1
  for path,h in receipt['sourceHashes'].items():assert sha(git('show',commit+':'+path))==h
 else:
  assert receipt['event']=='GUARDED ARTIFACT COMMIT'
  assert not receipt['authorizedCommentRepairs']
  for path in changed:
   assert not path.endswith('.idr')
   assert sha(git('show',commit+':'+path))==receipt['artifactHashes'][path]
header_repairs=json.loads((ROOT/'research-tests/O6-L2R7-HEADER-REPAIRS.json').read_text())
assert {r['path'] for r in header_repairs}=={p for p in DOC_EXCEPTIONS if p.startswith('research-tests/run-l2r6-')}
for repair in header_repairs:
 before=git('show',BASE+':'+repair['path']);after=(ROOT/repair['path']).read_bytes()
 assert sha(before)==repair['beforeSHA256'] and sha(after)==repair['afterSHA256']
 assert before.count(repair['old'].encode())==1 and after==before.replace(repair['old'].encode(),repair['new'].encode())
 old_ast=ast.parse(before);new_ast=ast.parse(after);old_ast.body=old_ast.body[1:];new_ast.body=new_ast.body[1:]
 assert ast.dump(old_ast)==ast.dump(new_ast),'Header repair changed executable AST'
planpath='research-tests/O6-L2R7-FINAL-VALIDATION-PLAN.json'
assert (OUT/'final-validation-plan.json').read_bytes()==(ROOT/planpath).read_bytes()
plan=json.loads((ROOT/planpath).read_text());assert len(plan)==17
assert len({p['path'] for p in plan})==len({p['unit'] for p in plan})==len(plan)
plancommits=git('log','--format=%H',BASE+'..HEAD','--',planpath).decode().splitlines();assert len(plancommits)==1
assert git('show',plancommits[0]+':'+planpath)==(ROOT/planpath).read_bytes()
assert bycommit[plancommits[0]]['timestampUTC']<=byunit[plan[0]['unit']]['start']
seen=set();modules={pathlib.Path(p['path']).stem:p['path'] for p in plan}
for item in plan:
 actual_deps={modules[n] for n in re.findall(r'^import DGamma\.(L2R7\w+)$',(ROOT/item['path']).read_text(),re.M)}
 assert set(item['dependsOn'])==actual_deps and actual_deps<=seen;seen.add(item['path'])
 r=byunit[item['unit']];assert r['passed'] and r['fresh'] and r['path']==item['path']
 assert r['sourceSHA256']==item['sourceHash']==sha((ROOT/item['path']).read_bytes())
assert seen=={str(p.relative_to(ROOT)) for p in (ROOT/OWNED/'DGamma').glob('*.idr')}
paths=git('diff','--name-only',BASE).decode().splitlines()
assert all(p in DOC_EXCEPTIONS or p.startswith(('research-tests/O6-L2R7-','research-tests/run-l2r7-')) for p in paths)
newdecls={}
for path in paths:
 if not path.endswith('.idr'):continue
 assert path.startswith(OWNED)
 assert subprocess.run(['git','show',BASE+':'+path],cwd=ROOT,capture_output=True).returncode!=0
 current=(ROOT/path).read_bytes();assert '%default total' in current.decode() and '%unbound_implicits off' in current.decode()
 assert not re.search(r'\b(believe_me|assert_total|postulate|assert_smaller|partial|with|let)\b|\?[A-Za-z_]',code(current))
 newdecls[path]=sorted(declarations(current));assert path in seen
assert sum(map(len,newdecls.values()))==len(sourcecommits)==57
origins=json.loads((OUT/'declaration-origins.json').read_text());assert len(origins)==57
for origin in origins:
 line=(ROOT/origin['path']).read_text().splitlines()[origin['line']-1]
 assert re.match(r'^(?:[01] |record |data )?'+re.escape(origin['declaration'])+r'\b',line)
 assert bycommit[origin['commit']]['invocation']==origin['check']
for letter,cap in [('A',22),('B',16),('C',12),('D',8)]:
 groups={}
 for r in records:
  match=re.fullmatch(letter+r'(\d+)-([1-3])',r['unit'])
  if match:groups.setdefault(int(match[1]),[]).append(r)
 assert set(groups)==set(range(1,cap+1))
 for n,group in groups.items():
  assert len(group)<=3
  assert [int(r['unit'].rsplit('-',1)[1]) for r in group]==list(range(1,len(group)+1))
  if letter=='A' and n==8:
   assert len(group)==3 and not any(r['passed'] for r in group)
  else:assert group[-1]['passed'] and sum(r['passed'] for r in group)==1
assert (OUT/'B2-1.source').read_bytes().rstrip()+b'\n'==(OUT/'V1.source').read_bytes()
assert byunit['V1']['passed'] and next(o for o in origins if o['unit']=='B2')['check']=='V1'
assert 'anyHitObserved' not in declarations((OUT/'A5-1.source').read_bytes()),'A4 was not fully reverted before bridges'
assert not any('elemDecConsObserved' in names for names in newdecls.values())
assert (ROOT/(OWNED+'DGamma/L2R7ReleaseDecode.idr')).read_bytes()==git('show','3ad23bd0:'+OWNED+'DGamma/L2R7ReleaseDecode.idr')
ledger=json.loads((ROOT/'research-tests/O6-L2R7-COMPILER-LEDGER.json').read_text())
archive=ROOT/'research-tests/O6-L2R7-COMPILER-EVIDENCE.tar.gz'
assert ledger['records']==records and ledger['recordCount']==len(records)
assert ledger['passedCount']==sum(r['passed'] for r in records) and ledger['evidenceArchiveSHA256']==sha(archive.read_bytes())
assert set(sourcecommits)<={r['resultingCommitHash'] for r in ledger['commitReceipts']}
with tarfile.open(archive,'r:gz') as tar:
 for r in records:
  for suffix in ['.json','.log','.source']:
   filename=r['unit']+suffix;assert tar.extractfile(OUT.name+'/'+filename).read()==(OUT/filename).read_bytes()
 for filename in ['final-validation-plan.json','shift.json','A8-stop.json','A4-defer.json','B2-whitespace.json','declaration-origins.json']:
  assert tar.extractfile(OUT.name+'/'+filename).read()==(OUT/filename).read_bytes()
 archived_receipts=[json.loads(s) for s in tar.extractfile(OUT.name+'/commit-receipts.jsonl').read().decode().splitlines()]
 assert receipts[:len(archived_receipts)]==archived_receipts
rehome=json.loads((ROOT/'research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json').read_text())
assert rehome['cp3Blob']==git('rev-parse','HEAD:src/DGamma/CP3.idr').decode().strip()
for path,h in rehome['checkedSourceSHA256'].items():assert sha((ROOT/path).read_bytes())==h
moved='\n'.join((ROOT/'src/DGamma/CP3.idr').read_text().splitlines()[2092:2120])+'\n';assert sha(moved.encode())==rehome['movedCombinedSHA256']
draft=(ROOT/'research-tests/O6-L2R5-CP3-DIFF-DRAFT.md').read_text()
for section in rehome['tier1Sections']:
 fragment=draft.split('### '+section['title']+'\n\n```idris\n',1)[1].split('```',1)[0];assert sha(fragment.encode())==section['sha256']
candidate=rehome['l2r7SameBundleControlsCandidate'];assert sha((ROOT/candidate['source']).read_bytes())==candidate['sourceSHA256']
fragment=draft.split('### T1.C — ',1)[1].split('```idris\n',1)[1].split('```',1)[0];assert sha(fragment.encode())==candidate['fragmentSHA256']
assert 'NOT YET SIGNABLE' in draft and 'PARTIALLY CHECKED' in draft and 'GeneralAttachedNormalForm' in draft
mapping={};tree=ast.parse((ROOT/'research-tests/run-l2r5-draft.py').read_text())
for node in tree.body:
 if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='mapping' for t in node.targets):mapping.update(ast.literal_eval(node.value))
 if isinstance(node,ast.For) and isinstance(node.target,ast.Tuple) and [ast.unparse(t) for t in node.target.elts]==['a','b']:mapping.update(dict(ast.literal_eval(node.iter)))
assert mapping==rehome['renamings'] and len(mapping)==30
assert (ROOT/'research-tests/O6-L2R7-GRIND-SHIFT-AUDIT.md').read_text().splitlines()[0]=='L2R6 FINAL GATE at 87e9fb20 was ACCEPTED by the supervisor as an explicitly PARTIAL bounded milestone (first real native iteration instances closed); stand-down authorized; independent reviewer launched'
assert not git('diff',BASE,'--','src/','research/','dgamma.ipkg','README.md','NOTES.md','THM73-PLAN.md')
assert not git('diff',BASE,'--',*[f'research-tests/O6-L2R{n}-Sources/' for n in range(1,7)])
assert not git('diff','--cached','--name-only')
pending=git('diff','--name-only').decode().splitlines()+git('ls-files','--others','--exclude-standard').decode().splitlines()
if prepublication:assert all((p in DOC_EXCEPTIONS or p.startswith(('research-tests/O6-L2R7-','research-tests/run-l2r7-'))) and not p.endswith('.idr') for p in pending)
else:assert not pending
processes=subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines())
shift=json.loads((OUT/'shift.json').read_text())
assert all(r['start']<shift['attemptCutoff'] for r in records if re.fullmatch(r'[ABCD]\d+-[1-3]',r['unit']))
assert all(byunit[p['unit']]['start']<shift['validationCutoff'] for p in plan)
tests=json.loads((OUT/'evidence-tests.json').read_text());assert tests['status']=='PASS' and tests['testsRun']>=20
report=dict(status='PREPUBLICATION_PASS' if prepublication else 'PASS',head=git('rev-parse','HEAD').decode().strip(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),invocationCount=len(records),passedCount=sum(r['passed'] for r in records),failedCount=sum(not r['passed'] for r in records),finalCheckCount=len(plan),newDeclarationCount=57,newDeclarations=newdecls,proofCommitCount=57,allCommitsReceiptAuthenticated=True,allSourceHashesAndLogsAuthenticated=True,A8StoppedAndReverted=True,B2WhitespaceV1ReceiptAuthenticated=True,headerOnlyRepairsAuthenticated=True,immutableFinalPlanPublishedBeforeChecks=True,finalPlanLeafBeforeDependent=True,allFinalSourcesFreshlyChecked=True,allInvocationsSerialized=True,maxSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records),RSSQualification='250ms sampled, not continuous peak',archiveSHA256=sha(archive.read_bytes()),predecessorProofSourcesUntouched=True,authorizedPredecessorDocsOnly=sorted(DOC_EXCEPTIONS),originalTier1CodeHashesUnchanged=True,sameBundleCandidateHashVerified=True,all30RenamingsSerialized=True,productionAndFrozenResearchUntouched=True,sharedLockAndWindowNotInspected=True,noOwnCompiler=True,noStagedFiles=True,cleanTrackedTree=not bool(pending),independentHumanProofReviewRequired=True)
(OUT/('prepublication-verification.json' if prepublication else 'independent-verification.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='newDeclarations'},indent=2))
