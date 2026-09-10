#!/usr/bin/env python3
"""Read-only R204 machine authentication; NOT independent human proof review.
maximum sampled RSS over command-matching idris2 processes (single-process compiler; not an aggregate process-tree total; not OS high-water).
"""
import datetime, hashlib, importlib.util, json, pathlib, re, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; ART=ROOT/'research-tests'; OUT=pathlib.Path('/tmp/dgamma-r204'); START='9b532666'
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('contract',ART/'r204_evidence_contract.py'); c=importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
def blob(commit,path):return subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
policy_bytes=(OUT/'execution-policy.json').read_bytes(); policy=json.loads(policy_bytes)
assert policy_bytes==(ART/'O6-R204-EXECUTION-POLICY.json').read_bytes()
assert sha((ART/'run-r204-check.py').read_bytes())==policy['runnerSHA256']
assert len({r['unit'] for r in records})==len(records)
for i,r in enumerate(records):
    assert json.loads((OUT/(r['unit']+'.json')).read_text())==r
    c.validate_record(r,(OUT/(r['unit']+'.source')).read_bytes(),(OUT/(r['unit']+'.log')).read_text(),ROOT)
    c.validate_execution_policy(r,policy_bytes)
    assert not i or records[i-1]['end']<=r['start'], 'Own compiler overlap'
    assert r['rssLimitKiB']==(52 if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    assert r['start']<('2026-09-10T00:14:00' if re.fullmatch(r'V\d+',r['unit']) else '2026-09-09T23:59:00')
    command=['idris2','--build',str(ROOT/'dgamma.ipkg')] if r['path']=='package' else ['idris2','--source-dir',str(ROOT/'src'),'--source-dir',str(ROOT/'research')]+(['--source-dir',str(ROOT/'research-tests')] if r['path'].startswith('research-tests/') else [])+(['--show-implicits'] if r['unit']=='A15-2' else [])+['--check',str(ROOT/r['path'])]
    assert command==r['command'], 'Non-native/unauthorized compiler command'
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT']; assert len(source_receipts)==30
source_commits={r['resultingCommitHash'] for r in source_receipts}
for commit in git('rev-list',START+'..HEAD').splitlines():
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    if any(p.endswith('.idr') or p=='dgamma.ipkg' for p in paths):assert commit in source_commits, 'Unreceipted source commit'
for receipt in receipts:
    r=next(x for x in records if x['unit']==receipt['invocation'])
    assert r['passed'] and r['fresh'] and r['exit']==0 and not r['expectedDiagnostic']
    assert r['end']<=receipt['timestampUTC']
    assert [x for x in records if x['start']<receipt['timestampUTC']][-1]['unit']==r['unit'], 'Intervening compiler invocation'
    commit=receipt['resultingCommitHash']; path='dgamma.ipkg' if r['path']=='package' else r['path']; after=blob(commit,path)
    assert sha(after)==receipt['sourceHash']==r['sourceSHA256']
    assert subprocess.run(['git','merge-base','--is-ancestor',commit,'HEAD'],cwd=ROOT).returncode==0
    changed=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    if receipt['event']=='GUARDED COMMIT':
        assert changed==[path]
        before_result=subprocess.run(['git','show',commit+'^:'+path],cwd=ROOT,capture_output=True)
        before=before_result.stdout if before_result.returncode==0 else b''
        assert receipt['beforeSourceHash']==(sha(before) if before else None)
        if r['unit']=='U0a-2':
            c.validate_style_repair(before,after)
            assert 'R203 review P1 (style: no let aliases)' in receipt['message']
        else:
            old=c.declarations(before); new=c.declarations(after); assert old<=new and len(new-old)==1
            removed=[x[1:] for x in git('show','--format=','-U0',commit).splitlines() if x.startswith('-') and not x.startswith('---') and x[1:].strip() and not x[1:].lstrip().startswith(('|||','--','import '))]
            assert not removed, 'Previously committed non-doc code changed'
    else:
        assert receipt['event']=='GUARDED ARTIFACT COMMIT'
        assert all(p.startswith('research-tests/') and not p.endswith('.idr') or p in ['README.md','NOTES.md','THM73-PLAN.md'] for p in changed)
        assert set(changed)==set(receipt['paths'])==set(receipt['artifactHashes'])
        for p,h in receipt['artifactHashes'].items():
            assert sha(blob(commit,p))==h['after']
            before=subprocess.run(['git','show',receipt['beforeCommitHash']+':'+p],cwd=ROOT,capture_output=True)
            assert h['before']==(sha(before.stdout) if before.returncode==0 else None)
proofs=[r for r in records if re.fullmatch(r'[AB]\d+-\d+',r['unit'])]
expected=['B'+str(i)+'-'+str(j) for i in range(1,15) for j in range(1,3 if i==4 else 2)]+['A'+str(i)+'-'+str(j) for i in range(1,17) for j in range(1,4 if i in [3,15] else 2)]
assert [r['unit'] for r in proofs]==expected and len(proofs)==35
rejected=['U0a-1','B4-1','A3-1','A15-1','A15-2','A15-3']
assert [r['unit'] for r in records if not r['passed']]==rejected
unreceipted=[r['unit'] for r in proofs if r['passed'] and not any(x['invocation']==r['unit'] for x in source_receipts)]
assert unreceipted==['A3-2']
c.validate_superseded_pass((OUT/'A3-2.source').read_bytes(),(OUT/'A3-3.source').read_bytes())
assert not [r['unit'] for r in records if not re.fullmatch(r'(?:U0a-[12]|[AB]\d+-\d+|V0-CACHE|V\d+)',r['unit'])], 'C ineligible / unplanned compiler'
revert=json.loads((OUT/'A15-revert.json').read_text()); assert revert['status']=='STOP3/3; FULL REVERT' and revert['exactHeadBytes']
assert sha(blob(revert['revertedToCommit'],revert['path']))==revert['revertedSHA256']==sha((ROOT/revert['path']).read_bytes())
cache=next(r for r in records if r['unit']=='V0-CACHE'); assert cache['passed'] and cache['sourceSHA256']==revert['revertedSHA256']
assert cache['start']>revert['timeUTC'] and cache['end']<next(r['start'] for r in records if r['unit']=='A16-1')
assert (OUT/'V0-CACHE-authorization.txt').is_file()
assert not git('diff',START,'--','research/DGamma/CP5ProviderHeadObservedSpike.idr'), 'Exhausted generic D5 changed'
assert not git('diff',START,'--','research/DGamma/CP5O20GlobalActivationHistorySpike.idr'), 'R203 A13 structural rightHistory changed'
plan_bytes=(OUT/'final-validation-plan.json').read_bytes(); plan=json.loads(plan_bytes); scope=json.loads((ART/'O6-R204-VALIDATION-SCOPE.json').read_text())
assert sha(plan_bytes)==(OUT/'final-validation-plan.sha256').read_text().strip()==scope['planSHA256']
assert plan_bytes==(ART/'O6-R204-FINAL-VALIDATION-PLAN.json').read_bytes()
inventory=json.loads((ART/'O6-R203-ROOT-CONTRACT-COSTS.json').read_text())['entries']; assert len(inventory)==290
changed=[p for p in git('diff','--name-only',START,'--','research/','research-tests/DGamma/').splitlines() if p.endswith('.idr')]
assert len(changed)==9 and set(changed)==set(scope['changedPaths'])
invalidated={x['path'] for x in inventory}|set(changed); modules={}
for parent in ['research/DGamma','research-tests/DGamma']:
    for p in (ROOT/parent).glob('*.idr'):
        m=re.search(r'^module\s+([\w.]+)',p.read_text(),re.M)
        if m:assert m[1] not in modules; modules[m[1]]=str(p.relative_to(ROOT))
c.validate_plan(plan,lambda p:(ROOT/('dgamma.ipkg' if p=='package' else p)).read_bytes(),modules,invalidated)
old=json.loads((ART/'O6-R203-COMPILER-LEDGER.json').read_text())['records']; inherited={r['path'] for r in old if r['passed'] and r['path']!='package'}
assert len(inherited)==181 and all((ROOT/p).is_file() for p in inherited) and not scope['excludedInheritedApplicablePaths']
assert {x['path'] for x in plan}==inherited|set(changed)|{'package'} and len(plan)==190
assert len(set(changed)-inherited)==8 and set(scope['newPaths'])==set(changed)-inherited
assert sum(bool(i['expectedDiagnostic']) for i in plan)==7
launch_path=OUT/'final-validation-launched.json'
if launch_path.exists():
    launch=json.loads(launch_path.read_text())
    assert launch['executionPolicySHA256']==sha(policy_bytes) and launch['planSHA256']==sha(plan_bytes)
    assert sha(blob(launch['head'],'research-tests/run-r204-check.py'))==policy['runnerSHA256']==launch['runnerSHA256']
    assert sha((ART/'run-r204-final-validation.py').read_bytes())==launch['driverSHA256']
else:assert '--pre-validation' in sys.argv
completed=[]
for item in plan:
    r=next((x for x in records if x['unit']==item['unit']),None)
    if r:
        assert r['path']==item['path'] and r['sourceSHA256']==item['sourceHash'] and r['expectedDiagnostic']==item['expectedDiagnostic'] and r['symbol']==item['symbol']
        assert r['validationContinuationSHA256']==sha(plan_bytes)
        if r['passed']:completed.append(item['unit'])
    assert item['heavyLock'] is False
    for dependency,h in item.get('unchangedSeededResearchImports',{}).items():
        assert sha((ROOT/dependency).read_bytes())==h and (ROOT/dependency).read_bytes()==blob(START,dependency)
if '--require-final-complete' in sys.argv:
    assert len(completed)==190 and len(records)==228 and sum(r['passed'] for r in records)==222
    assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
for path in changed:assert any(r['path']==path and r['passed'] and r['sourceSHA256']==sha((ROOT/path).read_bytes()) for r in records), 'Changed source unchecked'
for report_name,expected_tests,test_script in [('contract-tests',27,'test_r204_evidence_contract.py'),('policy-contract-tests',10,'test_r204_policy_contract.py')]:
    report=json.loads((OUT/(report_name+'.json')).read_text()); log=(OUT/(report_name+'.log')).read_text()
    assert report['status']=='PASS' and report['tests']==expected_tests and sha(log.encode())==report['logSHA256']
    assert re.search(r'Ran '+str(expected_tests)+r' tests',log) and log.rstrip().endswith('OK')
    assert sha((ART/test_script).read_bytes())==report['testSourceSHA256'] and sha((ART/'r204_evidence_contract.py').read_bytes())==report['contractSourceSHA256']
D_commits=[git('show','-s','--format=%s',r['resultingCommitHash']).strip() for r in receipts if re.match(r'R204 D[1-4]:',git('show','-s','--format=%s',r['resultingCommitHash']))]
assert len(D_commits)<=4 and len({x.split(':',1)[0] for x in D_commits})==len(D_commits)
report=dict(status='PASS',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').strip(),invocations=len(records),expectedPASS=sum(r['passed'] for r in records),rejected=rejected,supersededPASS=unreceipted,sourceReceipts=30,proofSourceReceipts=29,bodyOnlyStyleReceipts=1,artifactReceipts=len(receipts)-30,finalCompleted=len(completed),finalTotal=190,finalPlanSHA256=sha(plan_bytes),inheritedApplicableSources=181,newSources=8,changedIdrisSources=9,sourceSnapshotsAuthenticated=True,sourceReceiptsAuthenticated=True,artifactBeforeAfterHashesAuthenticated=True,allSourceCommitsReceipted=True,oneTopLevelDeclarationPerProofCommit=True,styleRepairStatementUnchanged=True,allPriorCommittedNonDocCodeRetainedExceptExactStyleRepair=True,DCommits=D_commits,allChangedSourcesChecked=True,allPlannedTargetImportsTopological=True,compilerOverlap=False,resourceStops=[r['unit'] for r in records if r['resourceStopped']],mutations=[r['unit'] for r in records if r['targetMutationDetected']],noLockOperations=True,ownerPolicySHA256=sha(policy_bytes),microUnitAttempts={u:sum(r['unit'].rsplit('-',1)[0]==u for r in proofs) for u in dict.fromkeys(r['unit'].rsplit('-',1)[0] for r in proofs)},AUnits=16,AInvocations=20,ARetained=15,BUnits=14,BInvocations=15,BRetained=14,exhaustedAndReverted=['A15 two-path literal append equality','A15 narrowed left-path literal append equality'],authorizedCacheValidation='V0-CACHE; byte-identical reverted A14; not A16 attempt',CProofAttempts=0,noStagedFiles=not git('diff','--cached','--name-only').strip(),qualification='Read-only machine authentication, NOT independent human proof review. B exact present-vestigial selection/actual-chain disappearance/current-present count rebase proved; ALL-name cut and D5 OPEN. A actual paired Insert runtime histories, two retained-event chronology birth producers and conditional pair constructor proved; global zip/coverage/canonical position transport/predecessor cut/skips/whole histories/synchronization OPEN. A15 STOP3/3 fully reverted. C INELIGIBLE. Seeded validation, NOT cold.')
output=next((s for s in sys.argv[1:] if s.startswith('/tmp/')),str(OUT/'independent.json'))
pathlib.Path(output).write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps(report,indent=2))
