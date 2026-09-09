#!/usr/bin/env python3
"""Read-only R203 machine authentication. Not an independent human proof review.
Use --pre-validation before launch, or --require-final-complete after final checks.
"""
import datetime,hashlib,importlib.util,json,pathlib,re,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r203');ART=ROOT/'research-tests';START='77e94c81'
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('contract',ART/'r203_evidence_contract.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
policy_bytes=(OUT/'execution-policy.json').read_bytes();policy=json.loads(policy_bytes)
assert policy_bytes==(ART/'O6-R203-EXECUTION-POLICY.json').read_bytes()
assert sha((ART/'run-r203-check.py').read_bytes())==policy['runnerSHA256']
assert len({r['unit'] for r in records})==len(records)
for i,r in enumerate(records):
    assert json.loads((OUT/(r['unit']+'.json')).read_text())==r
    c.validate_record(r,(OUT/(r['unit']+'.source')).read_bytes(),(OUT/(r['unit']+'.log')).read_text(),ROOT)
    c.validate_execution_policy(r,policy_bytes)
    assert not i or records[i-1]['end']<=r['start'], 'Own compiler overlap'
    assert r['rssLimitKiB']==(52 if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    assert r['start']<('2026-09-09T22:03:00' if re.fullmatch(r'V\d+',r['unit']) else '2026-09-09T21:48:00')
    command=['idris2','--build',str(ROOT/'dgamma.ipkg')] if r['path']=='package' else ['idris2','--source-dir',str(ROOT/'src'),'--source-dir',str(ROOT/'research')]+(['--source-dir',str(ROOT/'research-tests')] if r['path'].startswith('research-tests/') else [])+['--check',str(ROOT/r['path'])]
    assert command==r['command'], 'Non-native/unauthorized command'
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==32
source_commits={r['resultingCommitHash'] for r in source_receipts}
for commit in git('rev-list',START+'..HEAD').splitlines():
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    if any(p.endswith('.idr') or p=='dgamma.ipkg' for p in paths):assert commit in source_commits, 'Unreceipted source commit'
for receipt in receipts:
    r=next(x for x in records if x['unit']==receipt['invocation'])
    assert r['passed'] and r['fresh'] and r['exit']==0 and not r['expectedDiagnostic']
    assert r['end']<=receipt['timestampUTC']
    assert [x for x in records if x['start']<receipt['timestampUTC']][-1]['unit']==r['unit'], 'Intervening compiler invocation'
    commit=receipt['resultingCommitHash'];path='dgamma.ipkg' if r['path']=='package' else r['path']
    after=subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
    assert sha(after)==receipt['sourceHash']==r['sourceSHA256']
    assert subprocess.run(['git','merge-base','--is-ancestor',commit,'HEAD'],cwd=ROOT).returncode==0
    changed=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    if receipt['event']=='GUARDED COMMIT':
        assert changed==[path]
        before=subprocess.run(['git','show',commit+'^:'+path],cwd=ROOT,capture_output=True)
        old=c.declarations(before.stdout if before.returncode==0 else b'');new=c.declarations(after)
        assert old<=new and len(new-old)==1
        removed=[x[1:] for x in git('show','--format=','-U0',commit).splitlines() if x.startswith('-') and not x.startswith('---') and x[1:].strip() and not x[1:].lstrip().startswith(('|||','--','import '))]
        assert not removed, 'A previously committed code line changed'
    else:assert receipt['event']=='GUARDED ARTIFACT COMMIT' and all(p.startswith('research-tests/') and not p.endswith('.idr') or p in ['README.md','NOTES.md','THM73-PLAN.md'] for p in changed)
proofs=[r for r in records if re.fullmatch(r'[AB]\d+-\d+',r['unit'])]
expected=[]
for category,twice in [('B',{4,9,10,13,16}),('A',{1,5,8,10,13,14})]:
    for i in range(1,17):
        expected.append(f'{category}{i}-1')
        if i in twice:expected.append(f'{category}{i}-2')
assert [r['unit'] for r in proofs]==expected
rejected=['B4-1','B9-1','B10-1','B13-1','A1-1','A5-1','A8-1','A10-1','A13-1','A14-1']
assert [r['unit'] for r in proofs if not r['passed']]==rejected
unreceipted=[r['unit'] for r in proofs if r['passed'] and not any(x['invocation']==r['unit'] for x in source_receipts)]
assert unreceipted==['B16-1']
c.validate_superseded_pass((OUT/'B16-1.source').read_bytes(),(OUT/'B16-2.source').read_bytes())
assert not [r['unit'] for r in records if not re.fullmatch(r'(?:[AB]\d+-\d+|V\d+)',r['unit'])], 'C ineligible / unplanned invocation'
assert not git('diff',START,'--','research/DGamma/CP5ProviderHeadObservedSpike.idr'), 'Old exhausted D5 changed'
plan_bytes=(OUT/'final-validation-plan.json').read_bytes();plan=json.loads(plan_bytes);scope=json.loads((ART/'O6-R203-VALIDATION-SCOPE.json').read_text())
assert sha(plan_bytes)==(OUT/'final-validation-plan.sha256').read_text().strip()==scope['planSHA256']
assert plan_bytes==(ART/'O6-R203-FINAL-VALIDATION-PLAN.json').read_bytes()
inventory=json.loads((ART/'O6-R202-ROOT-CONTRACT-COSTS.json').read_text())['entries'];assert len(inventory)==285
changed=[p for p in git('diff','--name-only',START,'--','research/','research-tests/DGamma/').splitlines() if p.endswith('.idr')]
assert len(changed)==5 and set(changed)==set(scope['changedPaths'])
invalidated={x['path'] for x in inventory}|set(changed);modules={}
for parent in ['research/DGamma','research-tests/DGamma']:
    for p in (ROOT/parent).glob('*.idr'):
        m=re.search(r'^module\s+([\w.]+)',p.read_text(),re.M)
        if m:assert m[1] not in modules;modules[m[1]]=str(p.relative_to(ROOT))
c.validate_plan(plan,lambda p:(ROOT/('dgamma.ipkg' if p=='package' else p)).read_bytes(),modules,invalidated)
old=json.loads((ART/'O6-R202-COMPILER-LEDGER.json').read_text())['records'];inherited={r['path'] for r in old if r['passed'] and r['path']!='package'}
assert len(inherited)==176 and all((ROOT/p).is_file() for p in inherited)
assert not scope['excludedInheritedApplicablePaths']
assert {x['path'] for x in plan}==inherited|set(changed)|{'package'} and len(plan)==182
assert len(set(changed)-inherited)==5 and set(scope['newPaths'])==set(changed)-inherited
launch_path=OUT/'final-validation-launched.json'
if launch_path.exists():
    launch=json.loads(launch_path.read_text())
    assert launch['executionPolicySHA256']==sha(policy_bytes) and launch['planSHA256']==sha(plan_bytes)
    assert sha(subprocess.check_output(['git','show',launch['head']+':research-tests/run-r203-check.py'],cwd=ROOT))==policy['runnerSHA256']==launch['runnerSHA256']
    assert sha((ART/'run-r203-final-validation.py').read_bytes())==launch['driverSHA256']
else:assert '--pre-validation' in sys.argv
completed=[]
for item in plan:
    r=next((x for x in records if x['unit']==item['unit']),None)
    if r:
        assert r['path']==item['path'] and r['sourceSHA256']==item['sourceHash'] and r['expectedDiagnostic']==item['expectedDiagnostic'] and r['symbol']==item['symbol']
        assert r['validationContinuationSHA256']==sha(plan_bytes)
        if r['passed']:completed.append(item['unit'])
    assert item['heavyLock'] is False
    for dependency,source_hash in item.get('unchangedSeededResearchImports',{}).items():
        assert sha((ROOT/dependency).read_bytes())==source_hash
        assert (ROOT/dependency).read_bytes()==subprocess.check_output(['git','show',START+':'+dependency],cwd=ROOT)
if '--require-final-complete' in sys.argv:
    assert len(completed)==182 and len(records)==225 and sum(r['passed'] for r in records)==215
    assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
for path in changed:assert any(r['path']==path and r['passed'] and r['sourceSHA256']==sha((ROOT/path).read_bytes()) for r in records), 'Changed source unchecked'
for report_name,expected_tests,test_script in [('contract-tests',24,'test_r203_evidence_contract.py'),('policy-contract-tests',10,'test_r203_policy_contract.py')]:
    test_report=json.loads((OUT/(report_name+'.json')).read_text());test_log=(OUT/(report_name+'.log')).read_text()
    assert test_report['status']=='PASS' and test_report['tests']==expected_tests
    assert sha(test_log.encode())==test_report['logSHA256'] and re.search(r'Ran '+str(expected_tests)+r' tests',test_log) and test_log.rstrip().endswith('OK')
    assert sha((ART/test_script).read_bytes())==test_report['testSourceSHA256']
    assert sha((ART/'r203_evidence_contract.py').read_bytes())==test_report['contractSourceSHA256']
D_commits=[git('show','-s','--format=%s',r['resultingCommitHash']).strip() for r in receipts if re.match(r'R203 D[1-4]:',git('show','-s','--format=%s',r['resultingCommitHash']))]
assert len(D_commits)<=4 and len({x.split(':',1)[0] for x in D_commits})==len(D_commits)
report=dict(status='PASS',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').strip(),invocations=len(records),expectedPASS=sum(r['passed'] for r in records),rejected=rejected,supersededPASS=unreceipted,supersededPASSCleanupExact=True,sourceReceipts=32,artifactReceipts=len(receipts)-32,finalCompleted=len(completed),finalTotal=182,finalPlanSHA256=sha(plan_bytes),inheritedApplicableSources=176,newSources=5,changedIdrisSources=5,sourceSnapshotsAuthenticated=True,sourceReceiptsAuthenticated=True,allSourceCommitsReceipted=True,oneTopLevelDeclarationPerProofCommit=True,allPriorCommittedNonDocCodeRetained=True,DCommits=D_commits,allChangedSourcesChecked=True,allPlannedTargetImportsTopological=True,compilerOverlap=False,resourceStops=[r['unit'] for r in records if r['resourceStopped']],mutations=[r['unit'] for r in records if r['targetMutationDetected']],noLockOperations=True,ownerPolicySHA256=sha(policy_bytes),microUnitAttempts={u:sum(r['unit'].rsplit('-',1)[0]==u for r in proofs) for u in dict.fromkeys(r['unit'].rsplit('-',1)[0] for r in proofs)},AUnits=16,AInvocations=22,ARetained=16,BUnits=16,BInvocations=21,BRetained=16,exhaustedAndReverted=[],CProofAttempts=0,noStagedFiles=not git('diff','--cached','--name-only').strip(),qualification='Read-only machine authentication, NOT independent human proof review. Whole retained-close producer and actual classified-generation deletion coverage are proved. Both original native activation chronologies/all their prefix positions and whole selected-lifecycle disappearance are proved. Canonical-prefix transport, ALL-name predecessor cuts, paired runtime occurrence histories, synchronization, per-class ALL-name rebase, D5 and convergence remain OPEN. Seeded direct validation, not cold.')
output=pathlib.Path(next((s for s in sys.argv[1:] if s.startswith('/tmp/')),str(OUT/'independent.json')));output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
