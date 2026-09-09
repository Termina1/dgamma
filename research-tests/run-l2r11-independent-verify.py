#!/usr/bin/env python3
"""Independent, compiler-free L2R11 evidence validator. Imports NO check/commit
runner. Recomputes transcript freshness, snapshots, git blob/declaration deltas,
receipts, caps, timing, final plan, protected scope and archived bytes.
This is mechanical verification, not the parent-owned mathematical review.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, re, subprocess, tarfile
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
PREFIX='research-tests/O6-L2R11-'
RAW=Path('/tmp/dgamma-l2r11')
BASE='0b31f43a'
BOOTSTRAP='research-tests/O6-L2R10-Sources/DGamma/L2R10ReleaseAgreement.idr'
CAPS={'A':14,'B':16,'C':14,'D':8}

def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def decls(data):
 text=data.decode()
 return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
def path_allowed(path):
 return '..' not in Path(path).parts and not Path(path).is_absolute() and (path.startswith(PREFIX+'Sources/') or path == BOOTSTRAP)
def code(data):return '\n'.join(line.split('--')[0] for line in data.decode().splitlines() if not line.lstrip().startswith('|||'))
def record_valid(r,data,log):
 assert path_allowed(r['path']) and r['path'].endswith('.idr')
 if r['path']==BOOTSTRAP:assert r['unit']=='V0'
 assert sha(data)==r['sourceSHA256']
 assert r['transcript']==log
 assert '%default total' in code(data)
 assert not re.search(r'\b(?:believe_me|assert_total|postulate|partial|with|let)\b|\?[A-Za-z_]',code(data))
 assert all(line==line.rstrip() for line in data.decode().splitlines())
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
 assert r['targetMtimeTouch']['path']==str(ROOT/r['path']) and not r['bundleSources']
 assert not r['heavyLockAcquired'] and not r['heavyLockEvents']
 assert not r.get('declaredHeavy'), 'No heavy check declared this shift'
 for p in r['separateCompilerObservations']:
  if r.get('overlapTimestampsOnly'):
   assert set(p)=={'firstObservedUTC','lastObservedUTC'}
   assert r['start']<=p['firstObservedUTC']<=p['lastObservedUTC']<=r['end']
  else:assert p['classification']!='lane2' and str(ROOT)+'/' not in p['command']
 guard=18
 if r['maxSampleRSSKiB']>guard*1024*1024:assert r['interrupted'] and not passed
 assert r['start']<=r['end']
 return passed

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
 for r in records:
  unit=r['unit'];data=stored[unit+'.source'];log=stored[unit+'.log'].decode()
  assert json.loads(stored[unit+'.json'])==r
  record_valid(r,data,log)
  if previous_end:assert previous_end<=r['start'],'Overlapping own compiler intervals'
  previous_end=r['end']
  match=re.fullmatch(r'([ABCD])(\d+)-([1-3])',unit)
  if match:
   lane,n,attempt=match.groups();assert int(n)<=CAPS[lane]
   group=lane+n;groups.setdefault(group,[]).append(r)
   assert len(groups[group])<=3 and sum(x['passed'] for x in groups[group])<=1
   before=retained.get(r['path'],b'')
   assert len(decls(data)-decls(before))==1 and not decls(before)-decls(data)
   if r['passed']:retained[r['path']]=data
  else:assert re.fullmatch(r'V\d+',unit)
 successful=[r for r in receipts if r['event']=='GUARDED COMMIT']
 assert len(successful)==sum(r['passed'] for rows in groups.values() for r in rows)
 assert len({r['invocation'] for r in successful})==len(successful)
 assert {r['invocation'] for r in successful}=={r['unit'] for rows in groups.values() for r in rows if r['passed']}
 for rows in groups.values():assert [int(r['unit'].rsplit('-',1)[1]) for r in rows]==list(range(1,len(rows)+1))
 order=[(r['unit'][0],int(r['unit'].split('-')[0][1:])) for r in records if not r['unit'].startswith('V')]
 assert order==sorted(order), 'Ordered A then B then C then D'
 for receipt in receipts:
  r=byid[receipt['invocation']];assert r['passed'] and r['sourceSHA256']==receipt['sourceHash']
  assert r['end']<=receipt['timestampUTC']
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
 closed=json.loads(stored['source-closed.json']);assert closed['retainedDeclarations']==len(successful) and closed['newAttemptsForbidden']
 assert closed['head']==successful[-1]['resultingCommitHash']
 subprocess.run(['git','merge-base','--is-ancestor',closed['head'],manifest['boundaryHead']],cwd=ROOT,check=True)
 assert all(r['start']<closed['timestampUTC'] for r in records if not r['unit'].startswith('V'))
 shift=json.loads(stored['shift.json'])
 assert all(r['start']<(shift['validationCutoff'] if r['unit'].startswith('V') else shift['attemptCutoff']) for r in records)
 assert {k:sum(r['unit'].startswith(k) for r in successful) for k in CAPS}==closed['retainedByUnit']
 for path,data in retained.items():assert (ROOT/path).read_bytes()==data
 assert git('show',BASE+':'+BOOTSTRAP)==stored['V0.source']==(ROOT/BOOTSTRAP).read_bytes()
 for group in ['A7','C14']:
  assert len(groups[group])==3 and not any(x['passed'] for x in groups[group])
 changed=git('diff','--name-only',BASE,'HEAD').decode().splitlines()
 untracked=git('ls-files','--others','--exclude-standard').decode().splitlines()
 assert all(p.startswith((PREFIX,'research-tests/run-l2r11-')) for p in changed+untracked)
 plan=json.loads((ROOT/(PREFIX+'FINAL-VALIDATION-PLAN.json')).read_text())
 plan_commit=git('log','--diff-filter=A','--format=%H','--',PREFIX+'FINAL-VALIDATION-PLAN.json').decode().splitlines()[-1]
 assert git('show',plan_commit+':'+PREFIX+'FINAL-VALIDATION-PLAN.json')==(ROOT/(PREFIX+'FINAL-VALIDATION-PLAN.json')).read_bytes()
 plan_time=int(git('show','-s','--format=%ct',plan_commit))
 assert plan_time<=datetime.datetime.fromisoformat(byid[plan['validations'][0]['unit']]['start']).timestamp()
 assert len(plan['validations'])==len(retained)
 assert {t['path'] for t in plan['validations']}==set(retained)
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
 processes=subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
 assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines())
 return dict(passed=True,checkedHead=git('rev-parse','HEAD').decode().strip(),verifierSHA256=sha(Path(__file__).read_bytes()),archiveBoundaryHead=manifest['boundaryHead'],derivedLedgersVerified=True,records=len(records),proofAttempts=sum(len(v) for v in groups.values()),retainedDeclarations=len(successful),failedAttempts=[r['unit'] for r in records if not r['passed']],guardedSourceCommits=len(successful),guardedReceipts=len(receipts),finalValidations=len(retained),archiveFiles=len(stored),archiveSHA256=manifest['archiveSHA256'],noStagedFiles=True,ownCompilerRunning=False,humanMathematicalReview='parent-owned, not performed by this script',scope=closed['scope'])

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--write-report',action='store_true');parser.add_argument('--compare-raw',action='store_true');args=parser.parse_args()
 result=verify(use_archive=not args.compare_raw)
 if args.write_report:(ROOT/(PREFIX+'INDEPENDENT-VERIFICATION.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
