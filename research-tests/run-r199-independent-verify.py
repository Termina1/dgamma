#!/usr/bin/env python3
"""Read-only independent source/log/commit/plan authentication; no Idris launched."""
import datetime,hashlib,importlib.util,json,pathlib,re,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r199');ART=ROOT/'research-tests';START='fdf96f9a'
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('contract',ART/'r199_evidence_contract.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
assert len({r['unit'] for r in records})==len(records)
for i,r in enumerate(records):
    assert json.loads((OUT/(r['unit']+'.json')).read_text())==r
    c.validate_record(r,(OUT/(r['unit']+'.source')).read_bytes(),(OUT/(r['unit']+'.log')).read_text(),ROOT)
    assert not i or records[i-1]['end']<=r['start'], 'Own compiler overlap'
    assert r['heavyLock'] and r['heavyLock'][0]['event']=='acquired' and r['heavyLock'][0]['lane']=='R199-main'
    assert r['rssLimitKiB']==(52 if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    assert r['start']<('2026-09-09T14:41:00' if re.fullmatch(r'V\d+',r['unit']) else '2026-09-09T14:26:00')
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==44
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
        old=c.declarations(before.stdout if before.returncode==0 else b'');new=c.declarations(after)
        assert old<=new and len(new-old)==1, 'Not exactly one new retained declaration'
        lines=git('show','--format=','-U0',commit).splitlines()
        removed_code=[x[1:] for x in lines if x.startswith('-') and not x.startswith('---') and x[1:].strip() and not x[1:].lstrip().startswith(('|||','--','import '))]
        assert not removed_code, 'A prior committed code line was rewritten/removed'
    else:assert all(p.startswith('research-tests/') and not p.endswith('.idr') or p in ['README.md','NOTES.md','THM73-PLAN.md'] for p in changed)
attempts={}
for r in records:
    m=re.fullmatch(r'([AB]\d+)-(\d+)',r['unit'])
    if m:attempts.setdefault(m[1],[]).append(r)
assert len([u for u in attempts if u.startswith('A')])==26 and len([u for u in attempts if u.startswith('B')])==18
assert sum(len(v) for u,v in attempts.items() if u.startswith('A'))==31
assert sum(len(v) for u,v in attempts.items() if u.startswith('B'))==21
for unit,runs in attempts.items():
    assert [int(r['unit'].rsplit('-',1)[1]) for r in runs]==list(range(1,len(runs)+1)) and len(runs)<=3
    if unit=='B3':
        assert len(runs)==2 and all(r['passed'] for r in runs)
        assert not any(x['invocation']=='B3-1' for x in receipts), 'Guard-rejected whitespace check was not committed'
        refusal=[json.loads(x) for x in (OUT/'guard-refusals.jsonl').read_text().splitlines()]
        assert any(x['invocation']=='B3-1' and x['gate']=='git diff --check' for x in refusal)
        assert (OUT/'B3-1.source').read_bytes().rstrip()==(OUT/'B3-2.source').read_bytes().rstrip(), 'Only EOF whitespace repair authorized'
        assert any(x['invocation']=='B3-2' for x in source_receipts)
    else:
        assert not any(r['passed'] for r in runs[:-1]) and runs[-1]['passed']
        assert any(x['invocation']==runs[-1]['unit'] for x in source_receipts)
assert not any(re.fullmatch(r'[CD]\d+-\d+',r['unit']) for r in records), 'C has no proof attempt; D is compiler-free documentation'
assert not git('diff',START,'--','research/DGamma/CP5ProviderHeadObservedSpike.idr'), 'R197 D5 remains exhausted/frozen'
plan_bytes=(OUT/'final-validation-plan.json').read_bytes();plan=json.loads(plan_bytes);scope=json.loads((ART/'O6-R199-VALIDATION-SCOPE.json').read_text())
assert sha(plan_bytes)==(OUT/'final-validation-plan.sha256').read_text().strip()==scope['planSHA256']
assert plan_bytes==(ART/'O6-R199-FINAL-VALIDATION-PLAN.json').read_bytes()
inventory=json.loads((ART/'O6-R198-ROOT-CONTRACT-COSTS.json').read_text())['entries'];assert len(inventory)==259
changed=[p for p in git('diff','--name-only',START,'--','research/','research-tests/DGamma/').splitlines() if p.endswith('.idr')]
assert len(changed)==7
invalidated={x['path'] for x in inventory}|set(changed);modules={}
for parent in ['research/DGamma','research-tests/DGamma']:
    for p in (ROOT/parent).glob('*.idr'):
        m=re.search(r'^module\s+([\w.]+)',p.read_text(),re.M)
        if m:assert m[1] not in modules;modules[m[1]]=str(p.relative_to(ROOT))
c.validate_plan(plan,lambda p:(ROOT/('dgamma.ipkg' if p=='package' else p)).read_bytes(),modules,invalidated)
old=json.loads((ART/'O6-R198-COMPILER-LEDGER.json').read_text())['records'];inherited={r['path'] for r in old if r['passed'] and r['path']!='package'}
assert len(inherited)==150 and all((ROOT/p).is_file() for p in inherited)
assert not scope['excludedInheritedApplicablePaths']
assert {x['path'] for x in plan}==inherited|set(changed)|{'package'} and len(plan)==158
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
    assert len(completed)==158 and len(records)==211 and sum(r['passed'] for r in records)==204
    assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
for path in changed:assert any(r['path']==path and r['passed'] and r['sourceSHA256']==sha((ROOT/path).read_bytes()) for r in records), 'Changed source unchecked'
locks=[json.loads(s) for s in (OUT/'lock-events.jsonl').read_text().splitlines()]
for r in records:
    acquired=[x for x in locks if x['event']=='acquired' and x['unit']==r['unit']];released=[x for x in locks if x['event']=='released' and x['unit']==r['unit']]
    assert len(acquired)==len(released)==1 and acquired[0]==r['heavyLock'][0]
    assert acquired[0]['timestampUTC']<=r['start']<=r['end']<=released[0]['timestampUTC']
assert json.loads((OUT/'contract-tests.json').read_text())['tests']==21
D_docs=[git('show','-s','--format=%s',r['resultingCommitHash']).strip() for r in receipts if r['event']=='GUARDED ARTIFACT COMMIT' and re.match(r'R199 D[1-4]:',git('show','-s','--format=%s',r['resultingCommitHash']))]
assert len(D_docs)<=4 and len({x.split(':',1)[0] for x in D_docs})==len(D_docs)
report=dict(status='PASS',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').strip(),invocations=len(records),expectedPASS=sum(r['passed'] for r in records),rejected=[r['unit'] for r in records if not r['passed']],sourceReceipts=len(source_receipts),artifactReceipts=len(receipts)-len(source_receipts),finalCompleted=len(completed),finalTotal=158,finalPlanSHA256=sha(plan_bytes),inheritedApplicableSources=150,newSources=7,sourceSnapshotsAuthenticated=True,sourceReceiptsAuthenticated=True,allSourceCommitsReceipted=True,oneDeclarationPerRetainedCommit=True,allPriorCommittedCodeLinesRetained=True,DDocumentationCommits=D_docs,allChangedSourcesChecked=True,allPlannedTargetImportsTopological=True,compilerOverlap=False,resourceStops=[r['unit'] for r in records if r['resourceStopped']],mutations=[r['unit'] for r in records if r['targetMutationDetected']],heavyLockAcquisitionAndReleaseAuthenticated=True,microUnitAttempts={u:len(v) for u,v in attempts.items()},AUnits=26,AInvocations=31,ARetained=26,BUnits=18,BInvocations=21,BRetained=18,exhaustedAndReverted=[],inheritedExhaustedUnchanged=['R197 D5'],CProofAttempts=0,DProofAttempts=0,noStagedFiles=not git('diff','--cached','--name-only').strip(),qualification='Read-only machine authentication, NOT independent human proof review. Seeded direct targets, not cold. RSS sample0 means no live capture, not zero peak. B3 includes a real compiler PASS rejected by whitespace commit guard, followed only by a fresh whitespace recheck. No synchronization/all-name producer or convergence closure is claimed.')
output=pathlib.Path(next((s for s in sys.argv[1:] if s.startswith('/tmp/')),str(OUT/'independent.json')));output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
