#!/usr/bin/env python3
"""Compiler-free independent audit of committed R186/R187 receipts and archives.
Run from any cwd: python3 -I research-tests/run-r187-verify-evidence.py
Never compiles, stages, edits sources, or deletes caches. The final archive's own
commit receipt necessarily lives outside that archive and is reported at gate.
"""
import collections
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import tarfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
def sha(data):
    return hashlib.sha256(data).hexdigest()
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)
def utc(text):
    return datetime.datetime.fromisoformat(text)
def declarations(data):
    text = data.decode()
    functions = re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:', text, re.M)
    types = re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)', text, re.M)
    return set(functions + types)

report = {}
for shift in ['R186', 'R187']:
    ledger = json.loads((ROOT / ('research-tests/O6-' + shift + '-COMPILER-LEDGER.json')).read_text())
    archive = ROOT / 'research-tests' / ledger['evidenceArchive']
    assert sha(archive.read_bytes()) == ledger['evidenceArchiveSHA256'], shift
    prefix = 'dgamma-' + shift.lower() + '/'
    records = ledger['records']
    assert len(records) == ledger['recordCount']
    assert len({r['invocation'] for r in records}) == len(records)
    raw = {}
    sources = {}
    with tarfile.open(archive, 'r:gz') as tar:
        for r in records:
            exact = json.loads(tar.extractfile(prefix + r['record']).read())
            source = tar.extractfile(prefix + r['source']).read()
            log = tar.extractfile(prefix + r['log']).read().decode()
            assert sha(source) == r['sourceHash'] == exact['sourceSHA256'], r['invocation']
            assert log == exact['transcript'], r['invocation']
            computed_fresh = exact['path'] == 'package' or ('Building DGamma.' + pathlib.Path(exact['path']).stem) in log
            assert exact['fresh'] == computed_fresh, r['invocation']
            diagnostic = exact['expectedDiagnostic']
            computed_pass = computed_fresh and not exact['interrupted'] and (
                exact['exit'] != 0 and diagnostic in log and (not exact.get('symbol') or exact['symbol'] in log)
                if diagnostic else exact['exit'] == 0 and 'Error:' not in log)
            assert exact['passed'] == computed_pass, r['invocation']
            assert exact['unit'] == r['invocation'] and exact['path'] == r['target']
            for field in ['passed', 'fresh', 'interrupted', 'exit', 'command', 'expectedDiagnostic']:
                assert r[field] == exact[field], (r['invocation'], field)
            raw[r['invocation']] = exact
            sources[r['invocation']] = source
            path = 'dgamma.ipkg' if r['target'] == 'package' else r['target']
            for commit in r['matchingSourceCommits']:
                assert sha(git('show', commit + ':' + path)) == r['sourceHash']
        assert ledger['passedCount'] == sum(r['passed'] for r in records)
        assert ledger['failedCount'] == sum(not r['passed'] for r in records)
        if shift == 'R187':
            qualifications = ledger['validationQualifications']
            assert qualifications['V3']['validValidation'] is False
            assert sources['V3'] == b''
            assert ledger['invalidValidationCount'] == 1
            assert ledger['qualifiedPassedCount'] == sum(r['passed'] and qualifications.get(r['invocation'], {}).get('validValidation', True) for r in records)
            for suffix in ['ttc', 'ttm']:
                assert tar.extractfile(prefix + 'probe-backup-CP5LocalDiamondSpike.' + suffix).read()
            cleanup = json.loads(tar.extractfile(prefix + 'probe-cleanup.json').read())
            assert len(cleanup['removed']) == 2 and cleanup['protectedConfluenceFilesRetained']
            for item in cleanup['removed']:
                assert 'Confluence' not in pathlib.Path(item['path']).name
                data = tar.extractfile(prefix + 'probe-backup-' + pathlib.Path(item['path']).name).read()
                assert len(data) == item['bytes'] and sha(data) == item['sha256']
    report[shift] = dict(records=len(records), rawPassed=ledger['passedCount'], nonPassed=ledger['failedCount'], archiveSHA256=ledger['evidenceArchiveSHA256'])
    if shift == 'R186':
        assert not ledger['commitReceipts'] and ledger['commitReceiptStatus'].startswith('not recorded')
        report[shift]['historicalCommitReceipts'] = 'not recorded; source byte matches are not immediate-commit chronology'
        continue
    ordered = sorted(raw.values(), key=lambda r: r['start'])
    for first, second in zip(ordered, ordered[1:]):
        assert utc(first['end']) <= utc(second['start']), (first['unit'], second['unit'])
    assert max(r['maxSampleRSSKiB'] for r in raw.values()) <= 48 * 1024 * 1024
    assert not any(r['interrupted'] for r in raw.values())
    receipts = ledger['commitReceipts']
    source_receipts = [r for r in receipts if r['event'] == 'GUARDED COMMIT']
    expected_units = {p + str(i) for p, first, last in [('A', 1, 12), ('B', 1, 16), ('C', 3, 8), ('D', 1, 16), ('E', 1, 16), ('F', 1, 14)] for i in range(first, last + 1)}
    assert len(source_receipts) == 80 and {r['unit'] for r in source_receipts} == expected_units
    proof_runs = [r for r in raw.values() if re.fullmatch(r'[A-F]\d+-\d+', r['unit'])]
    assert len(proof_runs) == 89
    grouped = collections.defaultdict(list)
    for r in proof_runs:
        unit, attempt = r['unit'].split('-')
        grouped[unit].append(int(attempt))
        assert utc(r['start']) < datetime.datetime(2026, 9, 8, 8, 43, 56, tzinfo=datetime.timezone.utc)
        assert b'%default total' in sources[r['unit']] and b'%unbound_implicits off' in sources[r['unit']]
        prior = [q for q in source_receipts if raw[q['invocation']]['path'] == r['path'] and utc(q['timestampUTC']) <= utc(r['start'])]
        commit = max(prior, key=lambda q: q['timestampUTC'])['resultingCommitHash'] if prior else ledger['startCommit']
        old = subprocess.run(['git', 'show', commit + ':' + r['path']], cwd=ROOT, capture_output=True)
        added = declarations(sources[r['unit']]) - declarations(old.stdout if old.returncode == 0 else b'')
        assert len(added) == 1, (r['unit'], added)
    assert set(grouped) == expected_units
    assert all(sorted(attempts) == list(range(1, max(attempts) + 1)) and max(attempts) <= 3 for attempts in grouped.values())
    declaration_results = []
    for receipt in source_receipts:
        invocation = receipt['invocation']
        r = raw[invocation]
        assert r['passed'] and r['fresh'] and r['exit'] == 0 and not r['interrupted'] and r['expectedDiagnostic'] is None
        assert invocation == receipt['unit'] + '-' + receipt['attempt']
        assert receipt['sourceHash'] == r['sourceSHA256']
        commit = receipt['resultingCommitHash']
        assert sha(git('show', commit + ':' + r['path'])) == r['sourceSHA256']
        assert utc(r['end']) <= utc(receipt['timestampUTC'])
        assert not any(utc(r['end']) <= utc(other['start']) < utc(receipt['timestampUTC']) for other in raw.values() if other['unit'] != invocation), invocation
        assert 'exact source SHA256' in receipt['guardChecksPassed'] and 'no post-staged files' in receipt['guardChecksPassed']
        previous = subprocess.run(['git', 'show', commit + '^:' + r['path']], cwd=ROOT, capture_output=True)
        before = previous.stdout if previous.returncode == 0 else b''
        added = declarations(sources[invocation]) - declarations(before)
        assert len(added) == 1, (invocation, added)
        declaration_results.append(dict(unit=receipt['unit'], declaration=next(iter(added)), commit=commit))
    raw_artifacts = [r for r in receipts if r['event'] == 'GUARDED ARTIFACT COMMIT']
    missing_schema = [r for r in raw_artifacts if not all(k in r for k in ['unit', 'attempt', 'sourceInvocation'])]
    assert len(missing_schema) == 1 and missing_schema[0]['invocation'] == 'R186-repair'
    validations = [r for r in records if r['invocation'].startswith('V') and r['invocation'] != 'V3']
    assert len(validations) == 30 and all(r['passed'] and r['fresh'] for r in validations)
    assert sum(r['expectedDiagnostic'] is not None for r in validations) == 2
    assert not git('diff', '--cached', '--name-only').strip()
    assert not git('diff', '34b21c9', '--', 'src/', 'dgamma.ipkg').strip()
    report[shift].update(qualifiedPassed=ledger['qualifiedPassedCount'], invalidValidationCount=1, validValidations=30, expectedNegativeValidations=2,
        sourceReceipts=80, proofInvocations=89, oneNewDeclarationPerProofInvocation=True, attemptCapsPassed=True, oneNewDeclarationPerSourceCommit=True, sourceDeclarations=declaration_results,
        serialized=True, interrupted=0, maximumRSSKiB=max(r['maxSampleRSSKiB'] for r in raw.values()),
        historicalSchemaQualification='one retained compiler-free Unit0 artifact receipt lacks separately named unit/attempt/sourceInvocation; not rewritten',
        finalArtifactReceiptQualification='archive cannot contain its own commit-time receipt; final live receipt must be reported separately')
print(json.dumps(report, indent=2))
