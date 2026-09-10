#!/usr/bin/env python3
"""Compiler-free L2R16 mechanical verifier, adapted from L2R15 independent
verification contract. Imports NO check/commit runner. Recomputes source/log
hashes, own Building lines, quantities/TYPE status, budgets, source-commit
receipts, merge boundaries, seeded SupportSolution preservation, scope and
archive contents. This is NOT the parent-owned mathematical reviewer.
RSS = maximum sampled RSS over command-matching idris2 processes.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,re,subprocess,tarfile
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');RAW=Path('/tmp/dgamma-l2r16')
PREFIX='research-tests/O6-L2R16-'
BASE='a0e50ce016cc6a05fd8ee453803d975d7fdfa905'
PRODUCTION='452420c73c59a6af2d204cafa6e722b3a0fff995'
V19='bfe2e8d506f2ca77f2e96086f61ed19cc2bde642'
SUPPORT='build/ttc/2025081600/DGamma/CP4SupportSolution.ttc'
def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def decls(data):
 return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',data.decode(),re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',data.decode(),re.M))
def visibility_only(before,after,gate):
 assert sha(before)==gate['beforeSHA256'] and sha(after)==gate['afterSHA256']
 assert before.decode().count(gate['oldText'])==1
 assert after.decode()==before.decode().replace(gate['oldText'],gate['newText'])
 assert decls(before)==decls(after)
 return True

def bounded_requests(compiled,preflight,cap):
 requested=list(compiled)+list(preflight)
 assert len(set(requested))==len(requested)
 assert sorted(requested)==list(range(1,len(requested)+1))
 assert len(requested)<=cap
 return True

def type_status(record_or_data):
 return 'checked TYPE declaration; inhabitance reported separately' if record_or_data else 'checked TYPE expression; NOT an inhabitant'
def source_allowed(path,inventory):
 return path in inventory or bool(re.fullmatch(re.escape(PREFIX)+r'Sources/DGamma/L2R16\w+\.idr',path))
def record_valid(r,data,log,inventory):
 assert source_allowed(r['path'],inventory)
 assert sha(data)==r['sourceSHA256'] and r['transcript']==log
 assert '%default total' in data.decode()
 code='\n'.join(l.split('--')[0] for l in data.decode().splitlines() if not l.lstrip().startswith('|||'))
 assert not re.search(r'\b(?:believe_me|assert_total|partial|postulate)\b|\?[A-Za-z_]',code)
 if r['path'].startswith(PREFIX+'Sources/'):
  assert not re.search(r'\b(?:with|let)\b',code)
 assert all(l==l.rstrip() for l in data.decode().splitlines()) and data==data.rstrip()+b'\n'
 lines=re.findall(r'^\d+/\d+: Building .+$',log,re.M)
 pattern=r'^\d+/\d+: Building DGamma\.'+re.escape(Path(r['path']).stem)+r' \((?:'+re.escape(str(ROOT))+r'/)?'+re.escape(r['path'])+r'\)$'
 fresh=bool(re.search(pattern,log,re.M))
 assert lines==r['buildingLines'] and len(lines)==r['buildingCount'] and fresh==r['fresh']
 assert not r['expectedDiagnostic'] and not r['bundleSources']
 passed=fresh and len(lines)==1 and r['exit']==0 and 'Error:' not in log and not r['interrupted'] and not r['sourceMutationObserved']
 assert r['passed']==passed
 if r.get('deadlineInterrupted'):
  assert r['interrupted'] and not passed and r['end']>=r['deadlineStopUTC']
 assert r['command'][0]=='idris2' and r['command'][-2:]==['--check',str(ROOT/r['path'])]
 assert '--build' not in r['command'] and all('/Users/vyacheslavshebanov/Work/dgamma/' not in arg for arg in r['command'])
 assert r['targetMtimeTouch']['path']==str(ROOT/r['path'])
 assert r['rssLimitKiB']==(48 if r['declaredHeavy'] else 18)*1024*1024
 if r['maxSampleRSSKiB']>r['rssLimitKiB']:assert r['interrupted'] and not passed
 assert r['overlapTimestampsOnly']
 for x in r['separateCompilerObservations']:
  assert set(x)=={'firstObservedUTC','lastObservedUTC'}
  assert r['start']<=x['firstObservedUTC']<=x['lastObservedUTC']<=r['end']
 assert r['start']<=r['end']
 return passed

def verify(archive=False):
 assert Path.cwd()==ROOT
 if archive:
  manifest=json.loads((ROOT/(PREFIX+'RAW-EVIDENCE-MANIFEST.json')).read_text())
  a=ROOT/manifest['archive'];assert sha(a.read_bytes())==manifest['archiveSHA256']
  with tarfile.open(a,'r:gz') as tf:
   members=tf.getmembers();assert all(m.isfile() and m.name.startswith('raw/') and '..' not in m.name for m in members)
   stored={m.name[4:]:tf.extractfile(m).read() for m in members}
   assert len(stored)==len(members) and set(stored)==set(manifest['files'])
  for name,info in manifest['files'].items():assert sha(stored[name])==info['sha256'] and len(stored[name])==info['bytes']
  get=lambda name:stored[name]
 else:get=lambda name:(RAW/name).read_bytes()
 inventory=get('TARGETS.txt').decode().splitlines();assert len(inventory)==len(set(inventory))==200
 records=[json.loads(s) for s in get('ledger.jsonl').decode().splitlines()]
 receipts=[json.loads(s) for s in get('commit-receipts.jsonl').decode().splitlines()]
 decisions=json.loads(get('RECHECK-DECISIONS.json'));shift=json.loads(get('shift.json'))
 assert len({r['unit'] for r in records})==len(records)
 byid={r['unit']:r for r in records};prior=None;groups={}
 visibility=json.loads(get('VISIBILITY-COMPANION-AUTHORITY.json'))
 preflight=json.loads(get('T17-2-PREFLIGHT-REJECTION.json'))
 assert preflight['unit']=='T17-2' and preflight['compilerStarted'] is False
 assert preflight['unit'] not in byid
 assert sha(get('T17-2.preflight.source'))==preflight['sourceSHA256']
 assert 'START ' not in get('T17-2.wrapper.log').decode() and 'AssertionError' in get('T17-2.wrapper.log').decode()
 stopped=json.loads(get('T12-STOP.json'))
 assert stopped['attempts']==['T12-1','T12-2','T12-3']
 assert stopped['exhaustedName']=='L2R16 T12: UniqueRawNameInsertions on the anchor fixture via if-reduction'
 assert 'anchorUnique' not in decls((ROOT/stopped['path']).read_bytes())
 assert get('T12-FULL-REVERTED-SOURCE.idr')==get('T12-3.source')
 for r in records:
  record_valid(r,get(r['unit']+'.source'),get(r['unit']+'.log').decode(),inventory)
  assert json.loads(get(r['unit']+'.json'))==r
  if prior:assert prior<=r['start'], 'Overlapping lane checks'
  prior=r['end']
  assert shift['start'][:19]<=r['start'][:19]
  assert r['start']<(shift['validationCutoff'] if r['unit'].startswith('V') else shift['attemptCutoff'])
  if not r['unit'].startswith('V'):
   group=r['unit'].rsplit('-',1)[0];groups.setdefault(group,[]).append(r)
 for group,rs in groups.items():
  requested=[int(r['unit'].rsplit('-',1)[1]) for r in rs]
  assert sum(r['passed'] for r in rs)<=1
  cap=2 if group.startswith('R') and all('qualified' in c for c in decisions[rs[0]['path']]['changes']) else 3
  bounded_requests(requested,[2] if group=='T17' else [],cap)
  if group.startswith('S'):assert int(group[1:])<=40
  if group.startswith('T'):assert int(group[1:])<=26
 other_repairs=[d for d in decisions.values() if d.get('kind')=='lexical' and any('qualified' not in c for c in d['changes'])]
 assert len(other_repairs)<=40
 successful=[r for r in receipts if r['event']=='GUARDED COMMIT']
 assert {r['invocation'] for r in successful}==({r['unit'] for rs in groups.values() for r in rs if r['passed']} | {visibility['validation']})
 for receipt in successful:
  r=byid[receipt['invocation']];assert r['passed'] and r['sourceSHA256']==receipt['sourceHash']
  assert r['end']<=receipt['timestampUTC']
  assert not any(r['end']<other['start']<receipt['timestampUTC'] for other in records)
  assert receipt['paths']==[r['path']]
  commit=receipt['resultingCommitHash']
  changed=git('diff-tree','--no-commit-id','--name-only','-r',commit).decode().splitlines();assert changed==receipt['paths']
  data=git('show',commit+':'+r['path']);assert data==get(r['unit']+'.source')
  assert sha(data)==receipt['sourceHashes'][r['path']]
  previous=subprocess.run(['git','show',commit+'^:'+r['path']],cwd=ROOT,capture_output=True)
  before=previous.stdout if previous.returncode==0 else b''
  added=decls(data)-decls(before);removed=decls(before)-decls(data)
  if r['unit']==visibility['validation']:
   assert receipt['sourceAttempt']==visibility['sourceAttempt'] and receipt['unit']==visibility['repairUnit']
   assert r['path']==visibility['path']
   visibility_only(before,data,visibility)
   assert not added and not removed
  elif r['unit'].startswith('R'):
   assert not added and not removed
   d=decisions[r['path']]
   if all('qualified' in c for c in d['changes']):
    # Reverse ONLY the documented namespace prefixes, then compare code tokens.
    restored=data.decode()
    for c in sorted(d['changes'],key=lambda c:-len(c['qualified'])):
     assert c['qualified'].startswith('DGamma.') and not c['qualified'].startswith('DGamma.CP3.')
     restored=restored.replace(c['qualified'],c['name'])
    # Already-qualified predecessor references are not stripped below.
    original=before.decode()
    for c in sorted(d['changes'],key=lambda c:-len(c['qualified'])):original=original.replace(c['qualified'],c['name'])
    assert restored==original, 'Qualification-only diff changed other content'
   else:assert data==before.rstrip()+b'\n', 'Only other retained lexical class is EOF cleanup'
  elif r['unit'].startswith('S1-'):assert added=={'coreIntoAttached'} and removed=={'oldIntoAttached'}
  elif r['unit'].startswith('S2-'):assert added=={'StrictRootBeforeAnyLifecycle'} and not removed
  elif r['unit'].startswith('S'):assert not added and not removed
  else:assert len(added)==1 and not removed
 # Source and imported production boundaries are checked independently of merge messages.
 merge=get('MERGE-COMMIT.txt').decode().strip();v19merge=get('MERGE-V19-COMMIT.txt').decode().strip()
 assert git('rev-parse',merge+'^1').decode().strip()==BASE
 assert git('rev-parse',merge+'^2').decode().strip()==PRODUCTION
 assert git('rev-parse',v19merge+'^2').decode().strip()==V19
 assert git('rev-parse',merge+':src')==git('rev-parse',PRODUCTION+':src')
 assert get('PRE-MERGE-LANE-TREE.txt')==get('POST-MERGE-LANE-TREE.txt')
 assert git('diff',PRODUCTION,'HEAD','--','src')==b''
 assert git('show',V19+':research/DGamma/CP5ActorLifecycleOnlyExtended.idr')==(ROOT/'research/DGamma/CP5ActorLifecycleOnlyExtended.idr').read_bytes()
 seed=json.loads(get('RESEED-MANIFEST.json'));support=next(t for t in seed['ttcs'] if t['path']==SUPPORT)
 assert len(seed['ttcs'])==485 and sha((ROOT/SUPPORT).read_bytes())==support['sha256']
 assert (ROOT/SUPPORT).stat().st_mtime_ns==support['mtimeNs']
 assert support['sha256']=='0572d487cd7d341c091a94b5fa1d6d6685eade50c2b618f38ffc19fca7dce340'
 times=json.loads(get('SEED-MTIMES.json'));assert times['newMtimeNs']==1735689600000000000
 assert len(times['paths'])==741
 # Imported R206 notes/module changes are merge-only, never lane modifications.
 protected=['NOTES.md','README.md','THM73-PLAN.md','src/','research/DGamma/CP5ConfluenceLocalDiamondSpike.idr','research/DGamma/CP5ConfluenceCrossTraceSpike.idr','research/DGamma/CP5ConfluenceCanonicalSortSpike.idr','research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr','research/DGamma/CP5ConfluenceDeletionChainSpike.idr','research/DGamma/CP5O19*','research/DGamma/CP5O20*']
 assert not git('diff',V19,'HEAD','--',*protected)
 assert not git('diff','--cached','--name-only').strip()
 state=json.loads((ROOT/(PREFIX+'RECHECK-STATE.json')).read_text());assert state['total']==200
 assert sum(state['counts'].values())==200 and len(state['modules'])==200
 for row in state['modules']:
  assert sha((ROOT/row['path']).read_bytes())==row['sourceSHA256']
  if row['status'] in ['PASSED','REPAIRED']:
   r=byid[row['lastReceipt']];assert r['passed'] and r['sourceSHA256']==row['sourceSHA256']
  if row['status']=='BROKEN-BY-UNFREEZE':assert row['exactErrors']
 processes=subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
 assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines())
 return dict(passed=True,checkedHead=git('rev-parse','HEAD').decode().strip(),archiveVerified=archive,records=len(records),freshPasses=sum(r['passed'] for r in records),guardedSourceCommits=len(successful),repairGroups=len([g for g in groups if g.startswith('R')])+1,preflightOnlyRequests=['T17-2'],failedUnitsFullyReverted=['T12'],otherRepairsCapped40=len(other_repairs),semanticRestatements=[g for g in groups if g.startswith('S')],T2MicroUnits=[g for g in groups if g.startswith('T')],recheckCounts=state['counts'],noStagedFiles=True,ownCompilerRunning=False,supportSolutionSeedUntouched=True,humanMathematicalReview='parent-owned; not performed by this independent script')
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--archive',action='store_true');ap.add_argument('--write-report',action='store_true');a=ap.parse_args()
 result=verify(a.archive)
 if a.write_report:(ROOT/(PREFIX+'INDEPENDENT-VERIFICATION.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
