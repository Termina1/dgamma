#!/usr/bin/env python3
"""Read-only archive byte/record/source/log authentication; no extraction to disk."""
import hashlib,importlib.util,json,pathlib,subprocess,sys,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1];ART=ROOT/'research-tests';OUT=pathlib.Path('/tmp/dgamma-r203')
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('contract',ART/'r203_evidence_contract.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
sha=lambda b:hashlib.sha256(b).hexdigest()
archive=ART/'O6-R203-COMPILER-EVIDENCE.tar.gz';metadata=json.loads((ART/'O6-R203-EVIDENCE-VERIFICATION.json').read_text())
assert sha(archive.read_bytes())==metadata['archiveSHA256']
with tarfile.open(archive,'r:gz') as tar:
    members=tar.getmembers();names=[m.name for m in members]
    assert len(names)==len(set(names)) and all(m.isfile() for m in members)
    assert all(n.startswith('dgamma-r203/') and '..' not in n.split('/') for n in names)
    def data(path):
        member=tar.extractfile('dgamma-r203/'+path);assert member is not None
        return member.read()
    anchor=json.loads(data('archive-anchor.json'));archived_policy=data('execution-policy.json')
    assert anchor['anchorCommit']==metadata['anchorCommit']
    assert set(names)=={'dgamma-r203/'+p for p in anchor['filesSHA256']}|{'dgamma-r203/archive-anchor.json'}
    for path,digest in anchor['filesSHA256'].items():assert sha(data(path))==digest, path
    records=[json.loads(s) for s in data('ledger.jsonl').decode().splitlines()]
    assert len(records)==211 and sum(r['passed'] for r in records)==207
    assert len({r['unit'] for r in records})==len(records)
    for i,r in enumerate(records):
        assert json.loads(data(r['unit']+'.json'))==r
        c.validate_record(r,data(r['unit']+'.source'),data(r['unit']+'.log').decode(),ROOT)
        c.authenticate_policy_record(r,archived_policy,data('execution-policy-inherited-label.json'),json.loads(data('policy-label-correction.json')))
        assert not i or records[i-1]['end']<=r['start']
    receipts=[json.loads(s) for s in data('commit-receipts.jsonl').decode().splitlines()]
    source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==30
    assert sum(r.get('kind')=='authorized-comment-only' for r in source_receipts)==0
    for receipt in receipts:
        r=next(x for x in records if x['unit']==receipt['invocation'])
        assert r['passed'] and r['exit']==0 and r['sourceSHA256']==receipt['sourceHash']
        assert [x for x in records if x['start']<receipt['timestampUTC']][-1]['unit']==r['unit']
        path='dgamma.ipkg' if r['path']=='package' else r['path']
        assert sha(subprocess.check_output(['git','show',receipt['resultingCommitHash']+':'+path],cwd=ROOT))==receipt['sourceHash']
        assert subprocess.run(['git','merge-base','--is-ancestor',receipt['resultingCommitHash'],anchor['anchorCommit']],cwd=ROOT).returncode==0
    plan=json.loads(data('final-validation-plan.json'))
    assert len(plan)==177 and json.loads(data('final-validation-result.json'))['status']=='PASS'
    assert data('final-validation-plan.json')==(ART/'O6-R203-FINAL-VALIDATION-PLAN.json').read_bytes()
    for item in plan:
        r=next(x for x in records if x['unit']==item['unit'])
        assert r['passed'] and r['sourceSHA256']==item['sourceHash'] and r['expectedDiagnostic']==item['expectedDiagnostic'] and r['symbol']==item['symbol']
        path='dgamma.ipkg' if item['path']=='package' else item['path']
        assert sha(subprocess.check_output(['git','show',anchor['anchorCommit']+':'+path],cwd=ROOT))==item['sourceHash']
    correction=json.loads(data('policy-label-correction.json'))
    assert correction==json.loads((ART/'O6-R203-POLICY-LABEL-CORRECTION.json').read_text())
    assert data('execution-policy-inherited-label.json')==(ART/'O6-R203-EXECUTION-POLICY-INHERITED-LABEL.json').read_bytes()
    assert correction['priorInvocations']==[r['unit'] for r in records if r['start']<correction['timestampUTC']]

report=dict(status='PASS',anchorCommit=metadata['anchorCommit'],archiveSHA256=metadata['archiveSHA256'],allArchiveFilesVerified=len(members),nativeRecordsVerified=211,sourceSnapshotsVerified=211,rawLogsVerified=211,sourceReceiptsArchived=30,proofSourceReceiptsArchived=30,commentReceiptsArchived=0,artifactReceiptsArchived=len(receipts)-30,expectedPASS=207,rejectedSnapshots=4,finalChecksVerified=177,executionPolicySHA256=sha(archived_policy),ownerPolicyAuthenticated=True,metadataOnlyPolicyLabelHistoryAuthenticated=True,qualification='Read-only post-creation verification, not inside its own archive and not independent human review. Anchor deliberately excludes future publication/gate receipts.')
(OUT/'archive-verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
