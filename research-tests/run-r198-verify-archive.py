#!/usr/bin/env python3
"""Read-only full archive byte/record/source/log authentication; no extraction to disk."""
import hashlib,importlib.util,json,pathlib,subprocess,sys,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1];ART=ROOT/'research-tests';OUT=pathlib.Path('/tmp/dgamma-r198')
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('contract',ART/'r198_evidence_contract.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
sha=lambda b:hashlib.sha256(b).hexdigest()
archive=ART/'O6-R198-COMPILER-EVIDENCE.tar.gz'
metadata=json.loads((ART/'O6-R198-EVIDENCE-VERIFICATION.json').read_text())
assert sha(archive.read_bytes())==metadata['archiveSHA256']
with tarfile.open(archive,'r:gz') as tar:
    members=tar.getmembers();names=[m.name for m in members]
    assert len(names)==len(set(names)) and all(m.isfile() for m in members)
    assert all(n.startswith('dgamma-r198/') and '..' not in n.split('/') for n in names)
    def data(path):
        member=tar.extractfile('dgamma-r198/'+path);assert member is not None
        return member.read()
    anchor=json.loads(data('archive-anchor.json'))
    assert anchor['anchorCommit']==metadata['anchorCommit']
    assert set(names)=={'dgamma-r198/'+p for p in anchor['filesSHA256']}|{'dgamma-r198/archive-anchor.json'}
    for path,digest in anchor['filesSHA256'].items():assert sha(data(path))==digest, path
    records=[json.loads(s) for s in data('ledger.jsonl').decode().splitlines()]
    assert len(records)==202 and sum(r['passed'] for r in records)==195
    assert len({r['unit'] for r in records})==len(records)
    for r in records:
        assert json.loads(data(r['unit']+'.json'))==r
        c.validate_record(r,data(r['unit']+'.source'),data(r['unit']+'.log').decode(),ROOT)
    receipts=[json.loads(s) for s in data('commit-receipts.jsonl').decode().splitlines()]
    source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==41
    for receipt in receipts:
        r=next(x for x in records if x['unit']==receipt['invocation'])
        assert r['passed'] and r['exit']==0 and r['sourceSHA256']==receipt['sourceHash']
        path='dgamma.ipkg' if r['path']=='package' else r['path']
        assert sha(subprocess.check_output(['git','show',receipt['resultingCommitHash']+':'+path],cwd=ROOT))==receipt['sourceHash']
        assert subprocess.run(['git','merge-base','--is-ancestor',receipt['resultingCommitHash'],anchor['anchorCommit']],cwd=ROOT).returncode==0
    plan=json.loads(data('final-validation-plan.json'))
    assert len(plan)==151 and json.loads(data('final-validation-result.json'))['status']=='PASS'
    assert data('final-validation-plan.json')==(ART/'O6-R198-FINAL-VALIDATION-PLAN.json').read_bytes()
    for item in plan:
        r=next(x for x in records if x['unit']==item['unit'])
        assert r['passed'] and r['sourceSHA256']==item['sourceHash']
        path='dgamma.ipkg' if item['path']=='package' else item['path']
        assert sha(subprocess.check_output(['git','show',anchor['anchorCommit']+':'+path],cwd=ROOT))==item['sourceHash']
report=dict(status='PASS',anchorCommit=metadata['anchorCommit'],archiveSHA256=metadata['archiveSHA256'],allArchiveFilesVerified=len(members),nativeRecordsVerified=202,sourceSnapshotsVerified=202,rawLogsVerified=202,sourceReceiptsArchived=41,artifactReceiptsArchived=len(receipts)-41,expectedPASS=195,rejectedSnapshotsRetained=7,finalChecksVerified=151,qualification='Read-only post-creation verification; not claimed inside its own archive or as parent/reviewer acceptance. Anchor deliberately excludes future publication/gate receipts.')
(OUT/'archive-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
