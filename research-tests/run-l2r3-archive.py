#!/usr/bin/env python3
"""Archive a completed shift's exact invocation records without invoking Idris.
Usage: python3 -I research-tests/run-l2r3-archive.py L2R3 1893851e FINAL_HEAD [ADDENDUM]
matchingSourceCommits lists baseline/change commits whose target bytes match;
it is not a claim that every matching commit was made immediately after this run.
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import tarfile
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
shift, start, end = sys.argv[1:4]
assert sys.argv[4:] in [[], ['ADDENDUM']]
publication = '-ADDENDUM' if sys.argv[4:] else ''
assert shift=='L2R3' and start=='1893851e'
OUT = pathlib.Path('/tmp/dgamma-'+shift.lower())
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()
records = [json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
assert len({r['unit'] for r in records}) == len(records)
individual = {}
for p in OUT.glob('*.json'):
    d = json.loads(p.read_text())
    if isinstance(d, dict) and all(k in d for k in ['unit','path','command','start','end','sourceSHA256']):
        individual[d['unit']] = d
assert {r['unit'] for r in records} == set(individual)
invocation_qualifications = json.loads((OUT/'invocation-qualifications.json').read_text()) if (OUT/'invocation-qualifications.json').exists() else {}
assert set(invocation_qualifications).issubset(individual)
commits = {}
normalized = []
for r in records:
    assert r == individual[r['unit']], r['unit']
    assert (OUT/(r['unit']+'.source')).stat().st_size > 0, r['unit']
    assert sha((OUT/(r['unit']+'.source')).read_bytes()) == r['sourceSHA256']
    assert (OUT/(r['unit']+'.log')).read_text() == r['transcript']
    for extra in r.get('bundleSources', []):
        assert sha((OUT/extra['sourceFile']).read_bytes()) == extra['sourceSHA256']
    assert r['path'].startswith('research-tests/O6-L2R3-Sources/') or (r['unit'] in {'V0','V00'} and r['path']=='research-tests/O6-L2R2-Sources/DGamma/L2R2SmallStates.idr'), 'Lane-owned targets or authorized Unit0 validation only'
    target = r['path']
    if target not in commits:
        candidates = [start]+git('log','--format=%H',start+'..'+end,'--',target).decode().splitlines()
        commits[target] = []
        for c in candidates:
            found = subprocess.run(['git','show',c+':'+target],cwd=ROOT,capture_output=True)
            if found.returncode == 0:
                commits[target].append((git('rev-parse',c).decode().strip(),sha(found.stdout)))
    match = re.fullmatch(r'([A-Z]+\d+)-(\d+)',r['unit'])
    qualified = invocation_qualifications.get(r['unit'], {})
    normalized.append(dict(effectiveUnit=qualified.get('effectiveUnit', match[1] if match else r['unit']), effectiveAttempt=qualified.get('effectiveAttempt', int(match[2]) if match else None), invocation=r['unit'],unit=match[1] if match else r['unit'],attempt=int(match[2]) if match else None,
        target=r['path'],startUTC=r['start'],endUTC=r['end'],exit=r['exit'],fresh=r['fresh'],passed=r['passed'],
        interrupted=r['interrupted'],sourceHash=r['sourceSHA256'],matchingSourceCommits=[c for c,h in commits[target] if h==r['sourceSHA256']],
        command=r['command'],seconds=r['seconds'],maxSampleRSSKiB=r['maxSampleRSSKiB'],expectedDiagnostic=r['expectedDiagnostic'],symbol=r.get('symbol'),
        record=r['unit']+'.json',log=r['unit']+'.log',source=r['unit']+'.source',
        bundleSources=r.get('bundleSources', []), bundleFresh=r.get('bundleFresh', True),
        sourceMutationObserved=r['sourceMutationObserved'], targetMtimeTouch=r['targetMtimeTouch'],
        heavyLockAcquired=r['heavyLockAcquired'], heavyLockEvents=r['heavyLockEvents'],
        separateCompilerObservations=r['separateCompilerObservations']))
archive = ROOT/('research-tests/O6-'+shift+publication+'-COMPILER-EVIDENCE.tar.gz')
assert not archive.exists(), 'Published evidence archives are immutable; use a new gated publication name'
with tarfile.open(archive,'w:gz') as tar:
    for p in sorted(OUT.iterdir()):
        if p.is_file():
            tar.add(p,arcname=OUT.name+'/'+p.name)
with tarfile.open(archive,'r:gz') as tar:
    for r in records:
        for suffix in ['.json','.log','.source']:
            name=r['unit']+suffix
            assert tar.extractfile(OUT.name+'/'+name).read() == (OUT/name).read_bytes()
        for extra in r.get('bundleSources', []):
            assert tar.extractfile(OUT.name+'/'+extra['sourceFile']).read() == (OUT/extra['sourceFile']).read_bytes()
receipts = [json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()] if (OUT/'commit-receipts.jsonl').exists() else []
qualifications = json.loads((OUT/'validation-qualifications.json').read_text()) if (OUT/'validation-qualifications.json').exists() else {}
assert set(qualifications).issubset({r['unit'] for r in records})
dual_roles = json.loads((OUT/'final-validation-dual-roles.json').read_text()) if (OUT/'final-validation-dual-roles.json').exists() else {}
for unit, role in dual_roles.items():
    assert individual[unit]['passed'] and individual[unit]['fresh'] and individual[unit]['sourceSHA256'] == role['sourceHash']
ledger = dict(monitorQualifications=json.loads((OUT/'monitor-qualifications.json').read_text()), finalValidationDualRoles=dual_roles, invocationQualifications=invocation_qualifications, validationQualifications=qualifications,
    qualifiedPassedCount=sum(r['passed'] and qualifications.get(r['unit'], {}).get('validValidation', True) for r in records),
    invalidValidationCount=sum(not q.get('validValidation', True) for q in qualifications.values()),
    supersededHistoricalValidationCount=sum(q.get('superseded',False) for q in qualifications.values()),
    rawPassMeaning='passedCount preserves the runner outcome; qualifiedPassedCount excludes explicitly invalidated validation invocations without rewriting their exact records.',
    commitReceipts=receipts, commitReceiptStatus='recorded at commit' if receipts else 'not recorded; historical guarded commits are audit-asserted, not receipt-authenticated', shift=shift,generatedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),startCommit=git('rev-parse',start).decode().strip(),
    endCommit=git('rev-parse',end).decode().strip(),recordCount=len(normalized),passedCount=sum(r['passed'] for r in records),
    unitCaps={'A':24, 'B':12, 'C':14},
    publicationBoundary='The archive contains all source-commit receipts. Its own publication and later report-only commit receipts cannot be inside the archive without recursion; the independent verifier authenticates those from the append-only live receipt ledger.',
    failedCount=sum(not r['passed'] for r in records),interruptedCount=sum(r['interrupted'] for r in records),
    evidenceArchive=archive.name,evidenceArchiveSHA256=sha(archive.read_bytes()),
    matchingSourceCommitsMeaning='Baseline plus target-changing commits in (start,end], matched by SHA256. Byte matches, including the baseline, are independent of PASS/commit authorization; rejected unchanged targets (such as V0) may match the baseline.',
    sourceFreshMeaning='Target Building line is mandatory. Target-only mtime touches are supervisor-approved and individually logged; no package/cold builds permitted.',
    protocolIncidents=json.loads((OUT/'protocol-incidents.json').read_text()) if (OUT/'protocol-incidents.json').exists() else [], records=normalized)
(ROOT/('research-tests/O6-'+shift+publication+'-COMPILER-LEDGER.json')).write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps({k:v for k,v in ledger.items() if k!='records'},indent=2))
