#!/usr/bin/env python3
"""Read-only byte verification of every native record/source/log in the R196 archive."""
import hashlib,json,pathlib,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1];ART=ROOT/'research-tests';OUT=pathlib.Path('/tmp/dgamma-r196')
archive=ART/'O6-R196-COMPILER-EVIDENCE.tar.gz'
metadata=json.loads((ART/'O6-R196-EVIDENCE-VERIFICATION.json').read_text())
assert hashlib.sha256(archive.read_bytes()).hexdigest()==metadata['archiveSHA256']
with tarfile.open(archive,'r:gz') as tar:
    def data(path):
        member=tar.extractfile('dgamma-r196/'+path)
        assert member is not None
        return member.read()
    records=[json.loads(s) for s in data('ledger.jsonl').decode().splitlines()]
    assert len(records)==276
    for r in records:
        assert json.loads(data(r['unit']+'.json'))==r
        assert hashlib.sha256(data(r['unit']+'.source')).hexdigest()==r['sourceSHA256']
        assert data(r['unit']+'.log').decode()==r['transcript']
    receipts=[json.loads(s) for s in data('commit-receipts.jsonl').decode().splitlines()]
    assert len([r for r in receipts if r['event']=='GUARDED COMMIT'])==13
    assert len([r for r in records if r['passed']])==273
report=dict(status='PASS',anchorCommit=metadata['anchorCommit'],archiveSHA256=metadata['archiveSHA256'],nativeRecordsVerified=len(records),sourceSnapshotsVerified=len(records),rawLogsVerified=len(records),sourceReceiptsArchived=13,qualification='Read-only post-creation verification; not claimed inside the archive or as parent reviewer acceptance')
(OUT/'archive-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
