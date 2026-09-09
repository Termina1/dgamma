#!/usr/bin/env python3
"""Archive exact R195 records, snapshots, monitors and receipts without Idris.
Usage: python3 -I research-tests/run-r195-archive.py END_COMMIT
The anchor precedes the archive's own commit; no self-referential receipt claim.
"""
import datetime, hashlib, json, pathlib, re, subprocess, sys, tarfile
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r195')
START = '981e6137'
assert len(sys.argv) == 2
END = sys.argv[1]
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()
records = [json.loads(s) for s in (OUT / 'ledger.jsonl').read_text().splitlines()]
assert len({r['unit'] for r in records}) == len(records)
individual = {}
for path in OUT.glob('*.json'):
    data = json.loads(path.read_text())
    if isinstance(data, dict) and all(k in data for k in ['unit', 'path', 'command', 'start', 'end', 'sourceSHA256']):
        individual[data['unit']] = data
assert {r['unit'] for r in records} == set(individual)
commits, normalized = {}, []
for r in records:
    unit = r['unit']
    assert r == individual[unit]
    assert sha((OUT / (unit + '.source')).read_bytes()) == r['sourceSHA256']
    assert (OUT / (unit + '.log')).read_text() == r['transcript']
    target = 'dgamma.ipkg' if r['path'] == 'package' else r['path']
    if target not in commits:
        commits[target] = []
        candidates = [START] + git('log', '--format=%H', START + '..' + END, '--', target).decode().splitlines()
        for commit in candidates:
            found = subprocess.run(['git', 'show', commit + ':' + target], cwd=ROOT, capture_output=True)
            if found.returncode == 0:
                commits[target].append((git('rev-parse', commit).decode().strip(), sha(found.stdout)))
    match = re.fullmatch(r'([A-Z]+\d+)-(\d+)', unit)
    normalized.append(dict(invocation=unit, unit=match[1] if match else unit, attempt=int(match[2]) if match else None,
        target=r['path'], startUTC=r['start'], endUTC=r['end'], exit=r['exit'], fresh=r['fresh'], passed=r['passed'],
        interrupted=r['interrupted'], targetMutationDetected=r['targetMutationDetected'], sourceHash=r['sourceSHA256'],
        matchingSourceCommits=[c for c, h in commits[target] if h == r['sourceSHA256']], command=r['command'], seconds=r['seconds'],
        maxSampleRSSKiB=r['maxSampleRSSKiB'], rssLimitKiB=r['rssLimitKiB'], rssSamples=r['rssSamples'],
        expectedDiagnostic=r['expectedDiagnostic'], symbol=r.get('symbol'), record=unit + '.json', log=unit + '.log', source=unit + '.source',
        compilerScope=r['compilerScope'], lane2Compilers=r['lane2Compilers'], heavyLock=r['heavyLock']))
archive = ROOT / 'research-tests/O6-R195-COMPILER-EVIDENCE.tar.gz'
with tarfile.open(archive, 'w:gz') as tar:
    for path in sorted(OUT.iterdir()):
        if path.is_file(): tar.add(path, arcname=OUT.name + '/' + path.name)
with tarfile.open(archive, 'r:gz') as tar:
    for r in records:
        for suffix in ['.json', '.log', '.source']:
            name = r['unit'] + suffix
            assert tar.extractfile(OUT.name + '/' + name).read() == (OUT / name).read_bytes()
receipts = [json.loads(s) for s in (OUT / 'commit-receipts.jsonl').read_text().splitlines()]
ledger = dict(shift='R195', generatedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    startCommit=git('rev-parse', START).decode().strip(), endCommit=git('rev-parse', END).decode().strip(),
    recordCount=len(records), passedCount=sum(r['passed'] for r in records), failedCount=sum(not r['passed'] for r in records),
    interruptedCount=sum(r['interrupted'] for r in records), targetMutationCount=sum(r['targetMutationDetected'] for r in records),
    commitReceipts=receipts, commitReceiptStatus='recorded at each guarded commit; archive-own receipt necessarily excluded',
    evidenceArchive=archive.name, evidenceArchiveSHA256=sha(archive.read_bytes()),
    memoryMonitoringQualifications='1s sampled RSS, not OS high-water. Zero means no live sample captured. Samples retained in normalized and raw records.',
    successfulRecheckQualification='No successful proof recheck exception; every rejected snapshot retained.',
    matchingSourceCommitsMeaning='Baseline plus target-changing commits in (start,end], matched by SHA256. Empty for rejected/uncommitted bytes; matching is not immediate-commit attestation.',
    packageFreshMeaning='Successful seeded --build, not a forced/cold source rebuild. Source checks require their own Building line.',
    records=normalized)
(ROOT / 'research-tests/O6-R195-COMPILER-LEDGER.json').write_text(json.dumps(ledger, indent=2) + '\n')
print(json.dumps({k: v for k, v in ledger.items() if k not in ['records', 'commitReceipts']}, indent=2))
