#!/usr/bin/env python3
"""Copied from L2R14; independent, compiler-free L2R15 evidence validator. Imports NO check/commit
runner. Recomputes transcript freshness, snapshots, git blob/declaration deltas,
receipts, caps, timing, final plan, protected scope and archived bytes.
This is mechanical verification, not the parent-owned mathematical review.
RSS means maximum sampled RSS over command-matching idris2 processes, not an aggregate tree total, not OS high-water.
No visibility/body/comment companions are authorized in this shift.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, re, subprocess, tarfile
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
PREFIX='research-tests/O6-L2R15-'
RAW=Path('/tmp/dgamma-l2r15')
BASE='afa16946'
DOCUMENTARY_PATHS=set()
CAPS={'A':14,'B':16,'C':12}

def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def decls(data):
 text=data.decode()
 return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
def path_allowed(path):
 return bool(re.fullmatch(re.escape(PREFIX)+r'Sources/DGamma/L2R15[A-Za-z0-9]+\.idr',path))
def code(data):return '\n'.join(line.split('--')[0] for line in data.decode().splitlines() if not line.lstrip().startswith('|||'))
def record_valid(r,data,log):
 assert path_allowed(r['path']) and r['path'].endswith('.idr')
 assert sha(data)==r['sourceSHA256']
 assert r['transcript']==log
 assert re.search(r'^module DGamma\.'+re.escape(Path(r['path']).stem)+r'$',data.decode(),re.M)
 assert '%default total' in code(data)
 assert not re.search(r'\b(?:believe_me|assert_total|postulate|partial|with|let)\b|\?[A-Za-z_]',code(data))
 assert all(line==line.rstrip() for line in data.decode().splitlines())
 assert data==data.rstrip()+b'\n'
 lines=re.findall(r'^\d+/\d+: Building .+$',log,re.M)
 target=Path(r['path']).stem
 exact=r'^\d+/\d+: Building DGamma\.'+re.escape(target)+r' \((?:'+re.escape(str(ROOT))+r'/)?'+re.escape(r['path'])+r'\)$'
 fresh=bool(re.search(exact,log,re.M))
 assert lines==r['buildingLines'] and len(lines)==r['buildingCount'] and fresh==r['fresh']
 assert r['expectedDiagnostic'] is None
 passed=fresh and len(lines)==1 and r['exit']==0 and 'Error:' not in log and not r['interrupted'] and not r['sourceMutationObserved']
 assert passed==r['passed']
 assert r['command'][0]=='idris2' and r['command'][-2:]==['--check',str(ROOT/r['path'])]
 assert r['command'].count('--check')==1 and '--build' not in r['command']
 expected=['idris2','--source-dir',str(ROOT/'src'),'--source-dir',str(ROOT/'research'),'--source-dir',str(ROOT/'research-tests'),'--source-dir',str((ROOT/r['path']).parent.parent),'--check',str(ROOT/r['path'])]
 assert r['command']==expected, 'Only own seeded source roots allowed'
 assert r['targetMtimeTouch']['path']==str(ROOT/r['path']) and not r['bundleSources']
 assert not r['heavyLockAcquired'] and not r['heavyLockEvents']
 assert not r.get('declaredHeavy'), 'No heavy check declared this shift'
 assert r.get('overlapTimestampsOnly') is True
 for p in r['separateCompilerObservations']:
  assert set(p)=={'firstObservedUTC','lastObservedUTC'}
  assert r['start']<=p['firstObservedUTC']<=p['lastObservedUTC']<=r['end']
 guard=18
 if r['maxSampleRSSKiB']>guard*1024*1024:assert r['interrupted'] and not passed
 assert r['start']<=r['end']
 return passed

def apply_tier1_patch(base,patch):
 """Independently apply ONE textual CP3 unified diff in memory only."""
 source=base.splitlines(keepends=True); rows=patch.splitlines(keepends=True)
 assert rows[:2]==['--- a/src/DGamma/CP3.idr\n','+++ b/src/DGamma/CP3.idr\n']
 result=[]; cursor=0; i=2; hunks=0
 while i<len(rows):
  m=re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[^\n]*\n',rows[i]);assert m
  old_start=int(m[1])-1; old_count=int(m[2] or '1'); new_start=int(m[3])-1; new_count=int(m[4] or '1')
  assert cursor<=old_start<=len(source)
  result.extend(source[cursor:old_start]);cursor=old_start
  assert len(result)==new_start
  consumed=produced=0;i+=1;hunks+=1
  while i<len(rows) and not rows[i].startswith('@@ '):
   row=rows[i]; assert row and row[0] in ' +-'
   if row[0] in ' -':
    assert cursor<len(source) and source[cursor]==row[1:]
    cursor+=1;consumed+=1
   if row[0] in ' +':result.append(row[1:]);produced+=1
   i+=1
  assert consumed==old_count and produced==new_count
 assert hunks>0
 result.extend(source[cursor:]);return ''.join(result)

def declaration_kind(data,name):
 text=data.decode()
 if re.search(r'^(?:record|data)\s+'+re.escape(name)+r'\b',text,re.M):return 'type'
 declaration=re.search(r'^(?:[01] )?'+re.escape(name)+r'\s*:',text,re.M)
 assert declaration
 signature=text[declaration.end():].split('\n'+name,1)[0]
 if signature.rstrip().endswith('Type'):return 'type'
 return 'proof' if re.search(r'^0 '+re.escape(name)+r'\s*:',text,re.M) else 'executable'

def type_status(is_record):
 return 'checked TYPE declaration; inhabitance reported separately' if is_record else 'checked TYPE declaration; NOT inhabited'

def verify(use_archive=True):
 assert Path.cwd()==ROOT
 manifest=json.loads((ROOT/(PREFIX+'RAW-EVIDENCE-MANIFEST.json')).read_text())
 archive=ROOT/manifest['archive'];assert sha(archive.read_bytes())==manifest['archiveSHA256']
 with tarfile.open(archive,'r:gz') as tf:
  members=tf.getmembers();assert all(m.isfile() and m.name.startswith('raw/') and '..' not in m.name for m in members)
  stored={m.name[4:]:tf.extractfile(m).read() for m in members}
  assert len(stored)==len(members), 'Duplicate archive member'
 assert set(stored)==set(manifest['files'])
 for name,info in manifest['files'].items():
  assert sha(stored[name])==info['sha256'] and len(stored[name])==info['bytes']
  if not use_archive:assert (RAW/name).read_bytes()==stored[name]
 records=[json.loads(line) for line in stored['ledger.jsonl'].decode().splitlines()]
 receipts=[json.loads(line) for line in stored['commit-receipts.jsonl'].decode().splitlines()]
 assert len({r['unit'] for r in records})==len(records)
 byid={r['unit']:r for r in records};groups={};retained={};previous_end=None
 owner_ruling=json.loads(stored['D-OWNER-UNFREEZE-RULING.json'])
 assert owner_ruling['sameBundleControls'] and owner_ruling['postGateCompilerStandDown']
 assert sha(stored['D-OWNER-UNFREEZE-RULING.txt'])==owner_ruling['verbatimSHA256']
 assert b'RULING: (B)' in stored['D-OWNER-UNFREEZE-RULING.txt']
 inventory=json.loads(stored['CP3-REBUILD-INVENTORY.json'])
 assert (ROOT/(PREFIX+'CP3-REBUILD-INVENTORY.json')).read_bytes()==stored['CP3-REBUILD-INVENTORY.json']
 patch=(ROOT/(PREFIX+'CP3-TIER1-SIGNED-DIFF.patch')).read_bytes()
 assert patch==stored['CP3-TIER1-SIGNED-DIFF.patch'] and sha(patch)==inventory['patchSHA256']
 cp3=(ROOT/'src/DGamma/CP3.idr').read_bytes();assert sha(cp3)==inventory['cp3SHA256']
 candidate=apply_tier1_patch(cp3.decode(),patch.decode());assert sha(candidate.encode())==inventory['candidateSHA256']
 assert inventory['typecheckedInCP3'] is False and inventory['ownerSigned']=='2026-09-09'
 assert inventory['renames']['OrderedForcedRootBundleC']=='OrderedForcedRootBundle'
 assert inventory['renames']['ActorLifecycleOnlyAttachedC']=='ActorLifecycleOnly'
 assert candidate.count('ForcedBundleRetire :')==1 and candidate.count('ForcedBundleRemove :')==1
 assert 'OrderedForcedRootBundle nameEq selected core [] bundle' in candidate
 assert 'rootGenerationBeforeOwnLifecycle :' in candidate and 'allRootInputsFirst :' not in candidate
 assert 'originalFinal supportOrder original canonicalTrace' in candidate
 assert ''.join(cp3.decode().splitlines(keepends=True)[1999:2092]) in candidate
 tail=cp3.decode()[cp3.decode().index('record ConfluenceResult'):];assert candidate.endswith(tail)
 assert inventory['researchCount']==len(inventory['researchRecheck'])
 assert inventory['productionCount']==len(inventory['productionRecheck'])
 records_by_path={r['path']:r for r in inventory['researchRecheck']+inventory['productionRecheck']}
 modules_by_path={}
 for path in git('ls-files','*.idr').decode().splitlines():
  if not path.startswith(('src/','research/','research-tests/')):continue
  data=(ROOT/path).read_bytes();text=data.decode();m=re.search(r'^module\s+(\S+)',text,re.M)
  if m:modules_by_path[path]=(m[1],re.findall(r'^import\s+(?:public\s+)?(\S+)',text,re.M),data)
 affected={'DGamma.CP3'}
 while True:
  next_set=affected|{m for m,imports,data in modules_by_path.values() if any(dep in affected for dep in imports)}
  if next_set==affected:break
  affected=next_set
 assert set(records_by_path)=={path for path,(module,imports,data) in modules_by_path.items() if module in affected}
 for path,r in records_by_path.items():
  module,imports,data=modules_by_path[path]
  assert r['module']==module and r['imports']==imports and r['sourceSHA256']==sha(data)
 repair=[r['path'] for r in inventory['researchRecheck'] if r['oldSurfaceNames'] or r['productionNameCollisions'] or ('DGamma.CP3' in r['imports'] and r['unqualifiedRehomedNames'])]
 assert inventory['researchRepairCandidates']==repair
 overlay=(ROOT/(PREFIX+'CP3-DIFF-DRAFT-OVERLAY.md')).read_text()
 assert 'Tier 1 diff signable and signed by the owner on 2026-09-09; Tier 2 = open research obligations' in overlay
 assert '```diff\n'+patch.decode()+'```' in overlay
 assert all('`'+r['path']+'`' in overlay for r in inventory['researchRecheck'])
 scope_ruling=json.loads(stored['B-SCOPE-RULING.json'])
 assert scope_ruling['timestampUTC']<=byid['B1-1']['start']
 assert scope_ruling['cap']==16 and sha(stored['B-SCOPE-RULING-VERBATIM.txt'])==scope_ruling['verbatimSHA256']
 assert b'the scalar provision frame alone does not entail the global distance frames; structural scan transport is required and is the exact residue' in stored['B-SCOPE-RULING-VERBATIM.txt']
 for r in records:
  unit=r['unit'];data=stored[unit+'.source'];log=stored[unit+'.log'].decode()
  assert json.loads(stored[unit+'.json'])==r
  record_valid(r,data,log)
  if previous_end:assert previous_end<=r['start'],'Overlapping own compiler intervals'
  previous_end=r['end']
  match=re.fullmatch(r'([ABC])(\d+)-([1-3])',unit)
  if match:
   lane,n,attempt=match.groups();assert int(n)<=CAPS[lane]
   group=lane+n;groups.setdefault(group,[]).append(r)
   assert len(groups[group])<=3 and sum(x['passed'] for x in groups[group])<=1
   before=retained.get(r['path'],b'')
   assert len(decls(data)-decls(before))==1 and not decls(before)-decls(data)
   if r['passed']:retained[r['path']]=data
  else:
   assert re.fullmatch(r'V\d+',unit)
   assert int(unit[1:])>=1 and retained[r['path']]==data, 'Unchanged final validation only; no companion authorization exists'
 successful=[r for r in receipts if r['event']=='GUARDED COMMIT']
 assert len(successful)==sum(r['passed'] for rows in groups.values() for r in rows)
 assert len({r['invocation'] for r in successful})==len(successful)
 assert {r.get('sourceAttempt',r['invocation']) for r in successful}=={r['unit'] for rows in groups.values() for r in rows if r['passed']}
 for receipt in successful:
  origin=receipt.get('sourceAttempt',receipt['invocation'])
  assert origin==receipt['unit']+'-'+receipt['attempt']
  assert origin==receipt['invocation'] and not receipt.get('rstripOnlyRevalidation',False)
 for rows in groups.values():assert [int(r['unit'].rsplit('-',1)[1]) for r in rows]==list(range(1,len(rows)+1))
 order=[(r['unit'][0],int(r['unit'].split('-')[0][1:])) for r in records if not r['unit'].startswith('V')]
 assert order==sorted(order), 'Ordered A then B then C'
 for receipt in receipts:
  r=byid[receipt['invocation']];assert r['passed'] and r['sourceSHA256']==receipt['sourceHash']
  assert r['end']<=receipt['timestampUTC']
  assert {'no pre-staged files','no post-staged files'}<=set(receipt['guardChecksPassed'])
  assert not any(r['end']<other['start']<receipt['timestampUTC'] for other in records),'Intervening compiler before guarded commit'
  commit=receipt['resultingCommitHash']
  paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).decode().splitlines()
  assert set(paths)<=set(receipt['paths'])
  hashes=receipt.get('sourceHashes',receipt.get('artifactHashes',{}))
  for p,digest in hashes.items():assert sha(git('show',commit+':'+p))==digest
  if receipt['event']=='GUARDED COMMIT':
   assert receipt['paths']==[r['path']]
   assert git('show',commit+':'+r['path'])==stored[r['unit']+'.source']
   before=subprocess.run(['git','show',commit+'^:'+r['path']],cwd=ROOT,capture_output=True)
   old=before.stdout if before.returncode==0 else b''
   assert len(decls(stored[r['unit']+'.source'])-decls(old))==1
  assert receipt['event'] in {'GUARDED COMMIT','GUARDED ARTIFACT COMMIT'}
  assert not receipt.get('authorizedCommentRepairs')
 assert set(git('rev-list',BASE+'..'+manifest['boundaryHead']).decode().splitlines())=={r['resultingCommitHash'] for r in receipts}, 'Every boundary commit needs a guard receipt'
 closed=json.loads(stored['source-closed.json']);assert closed['retainedDeclarations']==len(successful) and closed['newAttemptsForbidden']
 assert closed['head']==successful[-1]['resultingCommitHash']
 assert closed['retainedModules']==len(retained)
 assert closed['statementAttemptGroups']==[{'name':'phaseReleaseHistoryDecoded','invocations':['A13-1','A13-2','A14-1']},{'name':'scanFilterPointwise','invocations':['B8-1','B8-2','B9-1']}]
 for attempt_group in closed['statementAttemptGroups']:
  assert len(attempt_group['invocations'])<=3
  for identity in attempt_group['invocations']:
   assert attempt_group['name'] in decls(stored[identity+'.source'])
  assert sum(byid[i]['passed'] for i in attempt_group['invocations'])==1
 subprocess.run(['git','merge-base','--is-ancestor',closed['head'],manifest['boundaryHead']],cwd=ROOT,check=True)
 assert all(r['start']<closed['timestampUTC'] for r in records if not r['unit'].startswith('V'))
 shift=json.loads(stored['shift.json'])
 assert all(shift['startUTC']<=r['start'] for r in records)
 assert all(r['start']<(shift['validationCutoff'] if r['unit'].startswith('V') else shift['attemptCutoff']) for r in records)
 assert {k:sum(r['unit'].startswith(k) for r in successful) for k in CAPS}==closed['retainedByUnit']
 for path,data in retained.items():assert (ROOT/path).read_bytes()==data
 stopped=[g for g,rows in groups.items() if len(rows)==3 and not any(x['passed'] for x in rows)]
 assert stopped==closed['stoppedGroups']
 assert git('branch','--show-current').decode().strip()=='cp5-thm73-lane-a8a10'
 changed=git('diff','--name-only',BASE,'HEAD').decode().splitlines()
 untracked=git('ls-files','--others','--exclude-standard').decode().splitlines()
 assert all(p.startswith((PREFIX,'research-tests/run-l2r15-')) or p in DOCUMENTARY_PATHS for p in changed+untracked)
 plan=json.loads((ROOT/(PREFIX+'FINAL-VALIDATION-PLAN.json')).read_text())
 plan_commit=git('log','--diff-filter=A','--format=%H','--',PREFIX+'FINAL-VALIDATION-PLAN.json').decode().splitlines()[-1]
 assert git('show',plan_commit+':'+PREFIX+'FINAL-VALIDATION-PLAN.json')==(ROOT/(PREFIX+'FINAL-VALIDATION-PLAN.json')).read_bytes()
 plan_time=int(git('show','-s','--format=%ct',plan_commit))
 assert plan_time<=datetime.datetime.fromisoformat(byid[plan['validations'][0]['unit']]['start']).timestamp()
 assert len(plan['validations'])==len(retained)
 assert {t['path'] for t in plan['validations']}==set(retained)
 positions={t['path']:i for i,t in enumerate(plan['validations'])}
 modules={re.search(r'^module (\S+)',(ROOT/p).read_text()).group(1):p for p in retained}
 for task in plan['validations']:
  deps=[modules[n] for n in re.findall(r'^import (\S+)',(ROOT/task['path']).read_text(),re.M) if n in modules]
  assert deps==task['directOwnDependencies'] and all(positions[d]<positions[task['path']] for d in deps)
 for task in plan['validations']:
  r=byid[task['unit']];assert r['passed'] and r['path']==task['path'] and r['sourceSHA256']==task['sourceSHA256']
  assert sha((ROOT/task['path']).read_bytes())==task['sourceSHA256']
 final=json.loads(stored['final-validation-result.json']);assert final['passed'] and len(final['validations'])==len(retained)
 assert final['validations']==[{k:byid[t['unit']][k] for k in ['unit','path','seconds','maxSampleRSSKiB']} for t in plan['validations']]
 micro=json.loads((ROOT/(PREFIX+'MICRO-UNIT-LEDGER.json')).read_text())
 assert micro['sourceBoundary']==closed and len(micro['sourceUnits'])==len(successful)
 for row,receipt in zip(micro['sourceUnits'],successful):
  r=byid[receipt['invocation']];data=stored[r['unit']+'.source']
  old=subprocess.run(['git','show',receipt['resultingCommitHash']+'^:'+r['path']],cwd=ROOT,capture_output=True)
  assert decls(data)-decls(old.stdout if old.returncode==0 else b'')=={row['name']}
  assert row['unit']==receipt['unit'] and row['invocation']==r['unit'] and row['commit']==receipt['resultingCommitHash']
  assert row['path']==r['path'] and row['checkedSourceSHA256']==r['sourceSHA256']
  assert row['currentSourceSHA256']==sha((ROOT/r['path']).read_bytes())
  assert row['kind']==declaration_kind((ROOT/r['path']).read_bytes(),row['name'])
  if row['kind']=='type':assert row['status']==type_status(bool(re.search(r'^(?:record|data)\s+'+re.escape(row['name'])+r'\b', (ROOT/r['path']).read_text(),re.M)))
  assert re.search(r'\b'+re.escape(row['name'])+r'\b',(ROOT/r['path']).read_text().splitlines()[row['line']-1])
 compiler=json.loads((ROOT/(PREFIX+'COMPILER-LEDGER.json')).read_text())
 assert compiler['boundaryHead']==manifest['boundaryHead'] and compiler['archiveSHA256']==manifest['archiveSHA256']
 assert compiler['guardedReceipts']==receipts and compiler['sourceDeclarations']==len(successful)
 assert len(compiler['invocations'])==len(records)
 for row,r in zip(compiler['invocations'],records):
  for k in ['unit','path','start','end','seconds','exit','passed','fresh','interrupted','sourceMutationObserved','sourceSHA256','maxSampleRSSKiB','buildingCount','buildingLines','expectedDiagnostic']:assert row[k]==r[k]
 overlaps=json.loads((ROOT/(PREFIX+'OVERLAP-LOG.json')).read_text())
 assert overlaps['timestampObservations']==[dict(invocation=r['unit'],firstObservedUTC=p.get('firstObservedUTC',r['start']),lastObservedUTC=p.get('lastObservedUTC',r['start'])) for r in records for p in r['separateCompilerObservations']]
 assert not git('diff','--cached','--name-only').strip()
 assert not git('diff','--name-only','--',PREFIX+'Sources/').strip()
 tests=json.loads(stored['evidence-tests-result.json'])
 test_count=len(re.findall(r'^ def test_', (ROOT/'research-tests/run-l2r15-evidence-tests.py').read_text(), re.M))
 assert tests['passed'] and tests['count']==test_count
 assert tests['verifierSHA256']==sha(Path(__file__).read_bytes())
 assert tests['testFileSHA256']==sha((ROOT/'research-tests/run-l2r15-evidence-tests.py').read_bytes())
 assert tests['logSHA256']==sha(stored[tests['logFile']]) and ('Ran '+str(test_count)+' tests').encode() in stored[tests['logFile']] and stored[tests['logFile']].rstrip().endswith(b'OK')
 processes=subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
 assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines())
 standdown=json.loads(stored['post-gate-compiler-standdown.json']);assert standdown['armedUTC']>=byid['V15']['end']
 probes=json.loads(stored['standdown-guard-probes.json'])
 assert probes['passed'] and probes['targetHashAndMtimeUnchanged'] and probes['noInvocationArtifacts']
 assert {p['entry'] for p in probes['probes']}=={'launch','check'}
 for probe in probes['probes']:
  assert probe['exit']!=0 and probe['expectedRejection'] and not probe['compilerInvoked']
  assert b'L2R15 post-gate stand-down' in stored[probe['log']]
  runner=(ROOT/('research-tests/run-l2r15-'+probe['entry']+'.py')).read_text()
  assert runner.index("assert not (ROOT/'research-tests/O6-L2R15-POST-GATE-STANDDOWN.json')")<runner.index('subprocess.Popen')
 assert not any(name.startswith('V9999') for name in stored)
 assert json.loads(stored['post-gate-compiler-standdown.json'])['armed']
 assert (ROOT/(PREFIX+'POST-GATE-STANDDOWN.json')).read_bytes()==stored['post-gate-compiler-standdown.json']
 return dict(tier1PatchAppliedInMemoryOnly=True,tier1CP3Typechecked=False,researchRecheckPaths=inventory['researchCount'],productionRecheckPaths=inventory['productionCount'],postGateCompilerStandDownArmed=True,passed=True,checkedHead=git('rev-parse','HEAD').decode().strip(),verifierSHA256=sha(Path(__file__).read_bytes()),archiveBoundaryHead=manifest['boundaryHead'],derivedLedgersVerified=True,focusedEvidenceTests=test_count,records=len(records),proofAttempts=sum(len(v) for v in groups.values()),retainedDeclarations=len(successful),failedAttempts=[r['unit'] for r in records if not r['passed']],guardedSourceCommits=len(successful),guardedReceipts=len(receipts),finalValidations=len(retained),archiveFiles=len(stored),archiveSHA256=manifest['archiveSHA256'],noStagedFiles=True,ownCompilerRunning=False,humanMathematicalReview='parent-owned, not performed by this script',scope=closed['scope'])

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--write-report',action='store_true');parser.add_argument('--compare-raw',action='store_true');args=parser.parse_args()
 result=verify(use_archive=not args.compare_raw)
 if args.write_report:(ROOT/(PREFIX+'INDEPENDENT-VERIFICATION.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
