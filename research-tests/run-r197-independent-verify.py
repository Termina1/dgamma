#!/usr/bin/env python3
"""Read-only independent record/commit/plan authentication; no Idris launched."""
import datetime,hashlib,importlib.util,json,pathlib,re,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r197');START='e2ebe3b5'
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('contract',ROOT/'research-tests/r197_evidence_contract.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
assert len({r['unit'] for r in records})==len(records)
for i,r in enumerate(records):
    assert json.loads((OUT/(r['unit']+'.json')).read_text())==r
    c.validate_record(r,(OUT/(r['unit']+'.source')).read_bytes(),(OUT/(r['unit']+'.log')).read_text(),ROOT)
    assert not i or records[i-1]['end']<=r['start'], 'Own compiler overlap'
    assert r['heavyLock'] and r['heavyLock'][0]['event']=='acquired' and r['heavyLock'][0]['lane']=='R197-main'
    assert r['rssLimitKiB']==(52 if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    assert r['start']<('2026-09-09T09:53:00' if re.fullmatch(r'V\d+',r['unit']) else '2026-09-09T09:38:00')
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT']
assert len(source_receipts)==33
source_commits={r['resultingCommitHash'] for r in source_receipts}
for commit in git('rev-list',START+'..HEAD').splitlines():
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    if any(p.endswith('.idr') or p=='dgamma.ipkg' for p in paths):assert commit in source_commits, 'Unreceipted source commit'
for receipt in receipts:
    r=next(x for x in records if x['unit']==receipt['invocation'])
    assert r['passed'] and r['fresh'] and r['exit']==0 and not r['expectedDiagnostic']
    assert r['end']<=receipt['timestampUTC']
    assert [x for x in records if x['start']<receipt['timestampUTC']][-1]['unit']==r['unit'], 'Intervening compiler before commit'
    commit=receipt['resultingCommitHash'];path='dgamma.ipkg' if r['path']=='package' else r['path']
    after=subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
    assert sha(after)==receipt['sourceHash']==r['sourceSHA256']
    changed=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    if receipt['event']=='GUARDED COMMIT':
        assert changed==[path]
        before=subprocess.run(['git','show',commit+'^:'+path],cwd=ROOT,capture_output=True)
        old=c.declarations(before.stdout if before.returncode==0 else b'')
        new=c.declarations(after)
        assert old<=new and len(new-old)==1, 'Not exactly one new retained declaration'
    else:assert all(p.startswith('research-tests/') and not p.endswith('.idr') or p in ['README.md','NOTES.md','THM73-PLAN.md'] for p in changed)
attempts={}
for r in records:
    m=re.fullmatch(r'([AD]\d+)-(\d+)',r['unit'])
    if m:attempts.setdefault(m[1],[]).append(r)
assert len([u for u in attempts if u.startswith('A')])==26
assert len([u for u in attempts if u.startswith('D')])==8
for unit,runs in attempts.items():
    assert [int(r['unit'].rsplit('-',1)[1]) for r in runs]==list(range(1,len(runs)+1)) and len(runs)<=3
    assert not any(r['passed'] for r in runs[:-1])
    if unit=='D5':assert len(runs)==3 and not any(r['passed'] for r in runs)
    else:assert runs[-1]['passed'] and any(x['invocation']==runs[-1]['unit'] for x in source_receipts)
assert not any(re.fullmatch(r'[BC]\d+-\d+',r['unit']) for r in records), 'B/C must have zero body/proof attempts'
revert=json.loads((OUT/'D5-exhausted-revert.json').read_text())
assert revert['remainingAttempts']==0 and revert['fourthAttemptProhibited']
assert sha((ROOT/'research/DGamma/CP5ProviderHeadObservedSpike.idr').read_bytes())==revert['restoredSourceSHA256']
plan_bytes=(OUT/'final-validation-plan.json').read_bytes();plan=json.loads(plan_bytes)
assert sha(plan_bytes)==(OUT/'final-validation-plan.sha256').read_text().strip()
assert plan_bytes==(ROOT/'research-tests/O6-R197-FINAL-VALIDATION-PLAN.json').read_bytes()
inventory=json.loads((ROOT/'research-tests/O6-R196-ROOT-CONTRACT-COSTS.json').read_text())['entries']
changed=[p for p in git('diff','--name-only',START,'--','research/','research-tests/DGamma/').splitlines() if p.endswith('.idr')]
invalidated={x['path'] for x in inventory}|set(changed)
modules={}
for parent in ['research/DGamma','research-tests/DGamma']:
    for p in (ROOT/parent).glob('*.idr'):
        m=re.search(r'^module\s+([\w.]+)',p.read_text(),re.M)
        if m:modules[m[1]]=str(p.relative_to(ROOT))
c.validate_plan(plan,lambda p:(ROOT/('dgamma.ipkg' if p=='package' else p)).read_bytes(),modules,invalidated)
old=json.loads((ROOT/'research-tests/O6-R196-COMPILER-LEDGER.json').read_text())['records']
inherited={r['path'] for r in old if r['passed'] and r['path']!='package'}
assert len(inherited)==136 and {x['path'] for x in plan}==inherited|set(changed)|{'package'}
completed=[]
for item in plan:
    r=next((x for x in records if x['unit']==item['unit']),None)
    if r:
        assert r['path']==item['path'] and r['sourceSHA256']==item['sourceHash'] and r['expectedDiagnostic']==item['expectedDiagnostic'] and r['symbol']==item['symbol']
        assert r['validationContinuationSHA256']==sha(plan_bytes)
        if r['passed']:completed.append(item['unit'])
    for dependency,source_hash in item.get('unchangedSeededResearchImports',{}).items():
        assert sha((ROOT/dependency).read_bytes())==source_hash
        assert (ROOT/dependency).read_bytes()==subprocess.check_output(['git','show',START+':'+dependency],cwd=ROOT)
if '--require-final-complete' in sys.argv:
    assert len(completed)==144
    assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
for path in changed:assert any(r['path']==path and r['passed'] and r['sourceSHA256']==sha((ROOT/path).read_bytes()) for r in records), 'Changed source unchecked'
locks=[json.loads(s) for s in (OUT/'lock-events.jsonl').read_text().splitlines()]
for r in records:
    acquired=[x for x in locks if x['event']=='acquired' and x['unit']==r['unit']]
    released=[x for x in locks if x['event']=='released' and x['unit']==r['unit']]
    assert len(acquired)==len(released)==1 and acquired[0]==r['heavyLock'][0]
    assert acquired[0]['timestampUTC']<=r['start']<=r['end']<=released[0]['timestampUTC']
report=dict(status='PASS',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').strip(),invocations=len(records),expectedPASS=sum(r['passed'] for r in records),rejected=[r['unit'] for r in records if not r['passed']],sourceReceipts=len(source_receipts),artifactReceipts=len(receipts)-len(source_receipts),finalCompleted=len(completed),finalTotal=144,finalPlanSHA256=sha(plan_bytes),inheritedApplicableSources=136,newSources=7,sourceSnapshotsAuthenticated=True,sourceReceiptsAuthenticated=True,allSourceCommitsReceipted=True,oneDeclarationPerRetainedCommit=True,allChangedSourcesChecked=True,compilerOverlap=False,resourceStops=[r['unit'] for r in records if r['resourceStopped']],mutations=[r['unit'] for r in records if r['targetMutationDetected']],heavyLockAcquisitionAndReleaseAuthenticated=True,microUnitAttempts={u:len(v) for u,v in attempts.items()},exhaustedAndReverted=['D5'],BCProofAttempts=0,noStagedFiles=not git('diff','--cached','--name-only').strip(),qualification='Read-only machine authentication, not an independent human proof review. Seeded direct targets, not cold build. RSS samples0 are no live capture, not zero actual peak. D5 optional consumer is NOT proved.')
output=pathlib.Path(next((s for s in sys.argv[1:] if s.startswith('/tmp/')),str(OUT/'independent.json')))
output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
