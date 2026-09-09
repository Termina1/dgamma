#!/usr/bin/env python3
"""Adapted from run-l2r7-independent-verify.py: independent evidence reconstruction.
Compiler-free, read-only git/source/record inspection; writes ONLY this lane's
verification reports. This is NOT independent human mathematical review.
"""
import ast,datetime,hashlib,json,pathlib,re,subprocess,sys,tarfile
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');OUT=pathlib.Path('/tmp/dgamma-l2r8');BASE='4469421e'
assert pathlib.Path.cwd()==ROOT
mode=sys.argv[1];assert mode in ['prepublication','published']
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def sha(b):return hashlib.sha256(b).hexdigest()
def declared(b):
 s=b.decode();return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',s,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',s,re.M))
def owned(p):return p.startswith(('research-tests/O6-L2R8-','research-tests/run-l2r8-')) or p in ['research-tests/O6-L2R5-CP3-DIFF-DRAFT.md','research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json']
assert git('branch','--show-current').decode().strip()=='cp5-thm73-lane-a8a10'
assert not git('diff','--cached','--name-only').strip()
changed=git('diff','--name-only',BASE,'HEAD').decode().splitlines();assert all(map(owned,changed))
assert all(owned(p) for p in git('diff','--name-only').decode().splitlines())
assert all(owned(p) for p in git('ls-files','--others','--exclude-standard').decode().splitlines())
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
assert len({r['unit'] for r in records})==len(records)
byid={r['unit']:r for r in records};groups={}
for r in records:
 u=r['unit'];assert json.loads((OUT/(u+'.json')).read_text())==r
 assert sha((OUT/(u+'.source')).read_bytes())==r['sourceSHA256']
 assert (OUT/(u+'.log')).read_text()==r['transcript']
 assert not r['bundleSources'] and not r['sourceMutationObserved']
 assert not r['heavyLockAcquired'] and r['heavyLockEvents']==[]
 assert r['maxSampleRSSKiB']<19*1024*1024
 assert all('/Users/vyacheslavshebanov/Work/dgamma/' not in arg for arg in r['command'])
 assert r['command'][0]=='idris2' and '--check' in r['command'] and '--build' not in r['command']
 assert r['command'][-1]==str(ROOT/r['path'])
 assert r['path'].startswith('research-tests/O6-L2R8-Sources/') or (u=='V0' and r['path']=='research-tests/O6-L2R7-Sources/DGamma/L2R7ReleaseDecode.idr')
 lines=re.findall(r'^\d+/\d+: Building .+$',r['transcript'],re.M);assert lines==r['buildingLines'] and len(lines)==r['buildingCount']
 if r['passed']:
  assert r['exit']==0 and r['fresh'] and not r['interrupted'] and len(lines)==1 and 'Error:' not in r['transcript']
  assert lines[0].endswith(f"DGamma.{pathlib.Path(r['path']).stem} ({ROOT/r['path']})")
 if re.fullmatch(r'[ABCD]\d+-[1-3]',u):groups.setdefault(u.rsplit('-',1)[0],[]).append(r)
 assert r['targetMtimeTouch']['path']==str(ROOT/r['path'])
for unit,attempts in groups.items():
 assert len(attempts)<=3 and [int(r['unit'].split('-')[1]) for r in attempts]==list(range(1,len(attempts)+1))
 assert sum(r['passed'] for r in attempts)<=1
 assert int(unit[1:])<={'A':10,'B':14,'C':8,'D':10}[unit[0]]
for letter,cap in {'A':10,'B':14,'C':5,'D':10}.items():assert {u for u in groups if u.startswith(letter)}=={letter+str(i) for i in range(1,cap+1)}
sourceReceipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(sourceReceipts)==37
origins=[]
for receipt in receipts:
 r=byid[receipt['invocation']];assert r['passed']
 prior=[x for x in records if x['end']<=receipt['timestampUTC']];assert prior[-1]['unit']==r['unit']
 commit=receipt['resultingCommitHash']
 if receipt['event']=='GUARDED COMMIT':
  path=r['path'];before=subprocess.run(['git','show',commit+'^:'+path],cwd=ROOT,capture_output=True).stdout;after=git('show',commit+':'+path)
  assert sha(after)==receipt['sourceHash']==r['sourceSHA256'] and after.startswith(before)
  names=declared(after)-declared(before);assert len(names)==1;name=next(iter(names))
  assert receipt['paths']==[path] and receipt['invocation'].startswith(('A','B','C','D'))
  origins.append({'unit':receipt['unit'],'declaration':name,'path':path,'check':receipt['invocation'],'commit':commit,'sourceSHA256':r['sourceSHA256']})
 else:
  for p,h in receipt['artifactHashes'].items():assert owned(p) and not p.endswith('.idr') and sha(git('show',commit+':'+p))==h
assert len([r for r in records if r['passed'] and r['unit'][0] in 'ABCD'])==len(sourceReceipts)
assert len(groups['A10'])==3 and not any(r['passed'] for r in groups['A10'])
assert len(groups['B3'])==2 and not any(r['passed'] for r in groups['B3'])
for unit,filename in [('A10','A10-stop.json'),('B3','B3-defer.json')]:
 d=json.loads((OUT/filename).read_text());assert not d['retained'];assert (ROOT/d['path']).read_bytes()==git('show',d['revertCommit']+':'+d['path'])
allNames=set().union(*(declared(p.read_bytes()) for p in (ROOT/'research-tests/O6-L2R8-Sources/DGamma').glob('*.idr')))
assert allNames=={r['declaration'] for r in origins}
assert not {'observedReleaseFixtures','contiguityNativeExecution','produceForcedRootPhases','produceAdmittedDistanceMove','normalizePhaseDistance','produceAttachedNormalForm'} & allNames
for p in (ROOT/'research-tests/O6-L2R8-Sources/DGamma').glob('*.idr'):
 s=p.read_text();assert '%default total' in s and '%unbound_implicits off' in s
 code='\n'.join(t.split('--')[0] for t in s.splitlines() if not t.lstrip().startswith('|||'))
 assert not re.search(r'\b(believe_me|assert_total|assert_smaller|postulate|partial|with|let)\b|\?[A-Za-z_]',code),p
for p in ROOT.glob('research-tests/run-l2r8-*.py'):ast.parse(p.read_text())
closure=json.loads((OUT/'source-closed.json').read_text());assert closure['boundary'].startswith('d11d13c0')
assert all(r['start']<closure['time'] for r in records if r['unit'][0] in 'ABCD')
plan=json.loads((OUT/'final-validation-plan.json').read_text());assert len(plan)==12
assert (OUT/'final-validation-plan.json').read_bytes()==(ROOT/'research-tests/O6-L2R8-FINAL-VALIDATION-PLAN.json').read_bytes()
planReceipt=next(r for r in receipts if 'research-tests/O6-L2R8-FINAL-VALIDATION-PLAN.json' in r['paths'])
for item in plan:
 r=byid[item['unit']];assert r['passed'] and r['path']==item['path'] and r['sourceSHA256']==item['sourceHash']==sha((ROOT/item['path']).read_bytes())
 assert r['start']>planReceipt['timestampUTC']
baseDraft=git('show',BASE+':research-tests/O6-L2R5-CP3-DIFF-DRAFT.md').decode();draft=(ROOT/'research-tests/O6-L2R5-CP3-DIFF-DRAFT.md').read_text()
assert re.findall(r'```idris\n(.*?)```',baseDraft,re.S)==re.findall(r'```idris\n(.*?)```',draft,re.S)
baseManifest=json.loads(git('show',BASE+':research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json'));manifest=json.loads((ROOT/'research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json').read_text())
assert all(manifest[k]==v for k,v in baseManifest.items()) and len(manifest['renamings'])==30
for p,h in manifest['checkedSourceSHA256'].items():assert sha((ROOT/p).read_bytes())==h
assert 'Ran 16 tests' in (OUT/'evidence-tests-final.txt').read_text() and '\nOK\n' in (OUT/'evidence-tests-final.txt').read_text()
ps=subprocess.check_output(['ps','-axo','pid=,ppid=,command='],text=True)
assert not any(str(ROOT)+'/' in row and '/idris2_app/idris2' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in ps.splitlines())
if mode=='published':
 ledger=json.loads((ROOT/'research-tests/O6-L2R8-COMPILER-LEDGER.json').read_text());archive=ROOT/'research-tests/O6-L2R8-COMPILER-EVIDENCE.tar.gz'
 assert ledger['records']==records and ledger['evidenceArchiveSHA256']==sha(archive.read_bytes())
 with tarfile.open(archive,'r:gz') as tar:
  for r in records:
   for suffix in ['.json','.log','.source']:
    f=r['unit']+suffix;assert tar.extractfile('dgamma-l2r8/'+f).read()==(OUT/f).read_bytes()
report={'mode':mode,'result':'PASS','head':git('rev-parse','HEAD').decode().strip(),'sourceBoundary':closure['boundary'],'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat(),'recordCount':len(records),'passedCount':sum(r['passed'] for r in records),'failedCount':sum(not r['passed'] for r in records),'retainedDeclarations':len(origins),'maximumSampleRSSKiB':max(r['maxSampleRSSKiB'] for r in records),'finalOwnTargetChecks':len(plan),'noStagedFiles':True,'noOwnCompiler':True,'changedFiles':changed,'checks':['all individual records/logs/source snapshots reconstructed','chronological fresh exact-source guarded receipts','one declaration and previous source bytes preserved at each source commit','A10 exact full revert; B3 exact deferred full revert','per-slot attempts/caps and source-closure boundary','immutable plan published before every final own-target check','all old Idris draft fragments and all30 renamings preserved','old source hashes and frozen paths unchanged','16 actual-AST compiler-free guard tests passed','no escape hatches/with/let or unchecked producer claims in retained sources','no main-tree/lock commands; sampled RSS <19 GiB','no staged files or own compiler'],'qualification':'Script-based independent reconstruction, NOT independent human mathematical review. Parent-owned reviewer gate remains required.'}
name='O6-L2R8-PREPUBLICATION-VERIFICATION' if mode=='prepublication' else 'O6-L2R8-INDEPENDENT-VERIFICATION'
(ROOT/f'research-tests/{name}.json').write_text(json.dumps(report,indent=2)+'\n')
(ROOT/f'research-tests/{name}.md').write_text('# L2R8 independent evidence reconstruction\n\n'+json.dumps(report,indent=2)+'\n\n'+report['qualification']+'\n')
(OUT/('declaration-origins-'+mode+'.json')).write_text(json.dumps(origins,indent=2)+'\n')
print(json.dumps(report,indent=2))
