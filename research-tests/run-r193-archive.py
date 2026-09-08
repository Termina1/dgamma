#!/usr/bin/env python3
"""Archive a completed shift's exact invocation records without invoking Idris.
Usage: python3 -I research-tests/run-r193-archive.py R193 77a9efe1 FINAL_HEAD
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
ROOT = pathlib.Path(__file__).resolve().parents[1]
shift, start, end = sys.argv[1:4]
assert shift=='R193' and start=='77a9efe1'
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
    target = 'dgamma.ipkg' if r['path'] == 'package' else r['path']
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
        compilerScope=r.get('compilerScope','serialized pre-parallel main lane'),lane2Compilers=r.get('lane2Compilers',[]),heavyLock=r.get('heavyLock',[])))
archive = ROOT/('research-tests/O6-'+shift+'-COMPILER-EVIDENCE.tar.gz')
with tarfile.open(archive,'w:gz') as tar:
    for p in sorted(OUT.iterdir()):
        if p.is_file():
            tar.add(p,arcname=OUT.name+'/'+p.name)
with tarfile.open(archive,'r:gz') as tar:
    for r in records:
        for suffix in ['.json','.log','.source']:
            name=r['unit']+suffix
            assert tar.extractfile(OUT.name+'/'+name).read() == (OUT/name).read_bytes()
receipts = [json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()] if (OUT/'commit-receipts.jsonl').exists() else []
qualifications = json.loads((OUT/'validation-qualifications.json').read_text()) if (OUT/'validation-qualifications.json').exists() else {}
assert set(qualifications).issubset({r['unit'] for r in records})
dual_roles = json.loads((OUT/'final-validation-dual-roles.json').read_text()) if (OUT/'final-validation-dual-roles.json').exists() else {}
for unit, role in dual_roles.items():
    assert individual[unit]['passed'] and individual[unit]['fresh'] and individual[unit]['sourceSHA256'] == role['sourceHash']
ledger = dict(finalValidationDualRoles=dual_roles, invocationQualifications=invocation_qualifications, validationQualifications=qualifications,
    qualifiedPassedCount=sum(r['passed'] and qualifications.get(r['unit'], {}).get('validValidation', True) for r in records),
    invalidValidationCount=sum(not q.get('validValidation', True) for q in qualifications.values()),
    supersededHistoricalValidationCount=sum(q.get('superseded',False) for q in qualifications.values()),
    rawPassMeaning='passedCount preserves the runner outcome; qualifiedPassedCount excludes explicitly invalidated validation invocations without rewriting their exact records.',
    commitReceipts=receipts, commitReceiptStatus='recorded at commit' if receipts else 'not recorded; historical guarded commits are audit-asserted, not receipt-authenticated', shift=shift,generatedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),startCommit=git('rev-parse',start).decode().strip(),
    endCommit=git('rev-parse',end).decode().strip(),recordCount=len(normalized),passedCount=sum(r['passed'] for r in records),
    failedCount=sum(not r['passed'] for r in records),interruptedCount=sum(r['interrupted'] for r in records),
    evidenceArchive=archive.name,evidenceArchiveSHA256=sha(archive.read_bytes()),
    matchingSourceCommitsMeaning='Baseline plus target-changing commits in (start,end], matched by SHA256; validation repeats can match the same source commit. Empty for rejected/uncommitted sources.',
    packageFreshMeaning='Inherited runner marks package fresh on successful seeded --build (no forced source rebuild); source checks require target Building line.',records=normalized)
(ROOT/('research-tests/O6-'+shift+'-COMPILER-LEDGER.json')).write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps({k:v for k,v in ledger.items() if k!='records'},indent=2))
