#!/usr/bin/env python3
"""Persist R179 exact per-attempt evidence and verify serialized intervals."""
import hashlib
import json
import pathlib
import subprocess
import tarfile
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r179')
records = [json.loads(line) for line in (OUT/'ledger.jsonl').read_text().splitlines()]
records.sort(key=lambda r:r['start'])
assert all(a['end'] <= b['start'] for a,b in zip(records,records[1:]))
for r in records:
    assert hashlib.sha256((OUT/(r['unit']+'.source')).read_bytes()).hexdigest() == r['sourceSHA256']
    assert (OUT/(r['unit']+'.log')).read_text() == r['transcript']
    history = subprocess.check_output(['git','log','--reverse','--format=%H','77577c2..HEAD','--',r['path']],cwd=ROOT,text=True).splitlines()
    r['matchingSourceCommits'] = []
    for commit in history:
        result = subprocess.run(['git','show',commit+':'+r['path']],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
        if result.returncode == 0 and hashlib.sha256(result.stdout).hexdigest() == r['sourceSHA256']:
            r['matchingSourceCommits'].append(commit)
(ROOT/'research-tests/O6-R179-COMPILER-LEDGER.json').write_text(json.dumps(records,indent=2)+'\n')
with tarfile.open(ROOT/'research-tests/O6-R179-COMPILER-EVIDENCE.tar.gz','w:gz') as archive:
    for r in records:
        for suffix in ['.source','.log','.json','.runner']:
            path = OUT/(r['unit']+suffix)
            if path.exists():
                archive.add(path,arcname=path.name)
summary = dict(checks=len(records),ordinaryPasses=sum(r['passed'] and not r['expectedDiagnostic'] for r in records),
    intendedNegativePasses=sum(r['passed'] and bool(r['expectedDiagnostic']) for r in records),
    rejectedOrInterrupted=sum(not r['passed'] for r in records),serialized=True,
    units=[dict(unit=r['unit'],passed=r['passed'],fresh=r['fresh'],seconds=r['seconds'],commits=r['matchingSourceCommits']) for r in records])
(OUT/'evidence-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
