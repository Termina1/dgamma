#!/usr/bin/env python3
"""Read-only independent authentication of R196 records, exact deltas and receipts."""
import datetime,hashlib,importlib.util,json,pathlib,re,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r196')
spec=importlib.util.spec_from_file_location('contract',ROOT/'research-tests/r196_evidence_contract.py')
contract=importlib.util.module_from_spec(spec);spec.loader.exec_module(contract)
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
assert len({r['unit'] for r in records})==len(records)
for i,r in enumerate(records):
    assert json.loads((OUT/(r['unit']+'.json')).read_text())==r
    contract.validate_record(r,(OUT/(r['unit']+'.source')).read_bytes(),(OUT/(r['unit']+'.log')).read_text(),ROOT)
    if i: assert records[i-1]['end']<=r['start'], 'Compiler overlap'
    assert r['heavyLock'] and r['heavyLock'][0]['event']==('acquired' if r['unit'].startswith(('C','S')) and r['unit']!='C3-1' else 'continuous-window-owned')
    assert r['heavyLock'][0]['lane']=='R196-main'
    assert r['rssLimitKiB']==(52 if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    cutoff='2026-09-09T07:19:35' if re.fullmatch(r'(?:B(?:\d+(?:R1)?|D\d+)|W\d+)',r['unit']) else '2026-09-09T07:04:35'
    assert r['start']<cutoff
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
manifest=json.loads((ROOT/'research-tests/O6-R196-ROOT-CONTRACT-EXECUTION.json').read_text())
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT']
source_commits={r['resultingCommitHash'] for r in source_receipts}
for commit in git('rev-list','58f88c63..HEAD').splitlines():
    paths=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    if any(p.endswith('.idr') or p=='dgamma.ipkg' for p in paths):
        assert commit in source_commits, 'Unreceipted source commit: '+commit
for receipt in receipts:
    source=next(r for r in records if r['unit']==receipt['invocation'])
    assert source['passed'] and source['fresh'] and source['exit']==0 and not source['expectedDiagnostic']
    assert source['end']<=receipt['timestampUTC']
    before_receipt=[r for r in records if r['start']<receipt['timestampUTC']]
    assert before_receipt[-1]['unit']==source['unit'], 'Intervening compiler before commit'
    commit=receipt['resultingCommitHash']; target='dgamma.ipkg' if source['path']=='package' else source['path']
    assert sha(subprocess.check_output(['git','show',commit+':'+target],cwd=ROOT))==receipt['sourceHash']==source['sourceSHA256']
    changed=git('diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    if receipt['event']=='GUARDED COMMIT':
        assert changed==[source['path']]
        item=next((x for x in manifest['items'] if x['unit']==receipt['unit']),None)
        if receipt['invocation']=='A4-2': item=json.loads((ROOT/'research-tests/O6-R196-A4-SYNTAX-AMENDMENT.json').read_text())
        if receipt['invocation']=='C3-1': item=json.loads((ROOT/'research-tests/O6-R196-C3-DELETION-HELPER-MANIFEST.json').read_text())
        if item:
            before=git('show',commit+'^:'+target)
            after=contract.apply_manifest_diff(before,item['diff'])
            assert sha(before.encode())==item['beforeSHA256'] and sha(after.encode())==item['afterSHA256']==source['sourceSHA256']
    else: assert all(p.startswith('research-tests/') and not p.endswith('.idr') or p in ['README.md','NOTES.md','THM73-PLAN.md'] for p in changed)
attempts={}
for r in records:
    m=re.fullmatch(r'([AC]\d+)-(\d+)',r['unit'])
    if m:attempts.setdefault(m[1],[]).append(r)
for unit,runs in attempts.items():
    assert [int(r['unit'].rsplit('-',1)[1]) for r in runs]==list(range(1,len(runs)+1)) and len(runs)<=3
    assert not any(r['passed'] for r in runs[:-1])
assert sum(len(v) for k,v in attempts.items() if k.startswith('A'))<=12
assert sum(len(v) for k,v in attempts.items() if k.startswith('C'))<=10
plan=json.loads((ROOT/'research-tests/O6-R196-DEPENDENT-RECHECK-CONTINUATION.json').read_text())
contract.validate_topology(plan['items'],plan['unitAPaths'])
completed=[]
for item in plan['items']:
    r=next((r for r in records if r['unit']==item['unit']),None)
    if r:
        assert r['path']==item['path'] and r['sourceSHA256']==item['sourceHash'] and r['expectedDiagnostic']==item['expectedDiagnostic'] and r['symbol']==item['symbol']
        if r['passed']:completed.append(item['unit'])
if '--require-B-complete' in sys.argv:assert len(completed)==133 and len(source_receipts)>=4
second_plan=json.loads((ROOT/'research-tests/O6-R196-SECOND-WINDOW-PLAN.json').read_text())
w_completed=[]
for item in second_plan['items']:
    r=next((r for r in records if r['unit']==item['unit']),None)
    if r:
        assert r['path']==item['path'] and r['sourceSHA256']==item['sourceHash'] and r['expectedDiagnostic']==item['expectedDiagnostic'] and r['symbol']==item['symbol']
        if r['passed']:w_completed.append(item['unit'])
if '--require-W-complete' in sys.argv:assert len(w_completed)==127
current_sources={p for p in git('diff','--name-only','58f88c63','--','research/','research-tests/DGamma/').splitlines() if p.endswith('.idr')}
for path in current_sources:
    assert any(r['path']==path and r['passed'] and r['sourceSHA256']==sha((ROOT/path).read_bytes()) for r in records), 'No current-source PASS: '+path
report=dict(timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').strip(),status='PASS',invocations=len(records),expectedPASS=sum(r['passed'] for r in records),sourceReceipts=len(source_receipts),artifactReceipts=len(receipts)-len(source_receipts),BCompleted=len(completed),BTotal=133,WCompleted=len(w_completed),WTotal=127,resourceStops=[r['unit'] for r in records if r.get('resourceStopped')],mutations=[r['unit'] for r in records if r['targetMutationDetected']],compilerOverlap=False,sourceReceiptsAuthenticated=True,sourceSnapshotsAuthenticated=True,allCurrentChangedSourcesChecked=True,allSourceCommitsReceipted=True,sampledRSSQualification='One-second own-worktree samples, not OS high-water; zero means no live sample captured',microUnitAttempts={k:len(v) for k,v in attempts.items()},noStagedFiles=not git('diff','--cached','--name-only').strip())
output=pathlib.Path(next((s for s in sys.argv[1:] if s.startswith('/tmp/')),str(OUT/'independent.json')))
output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
