#!/usr/bin/env python3
"""Compiler-free independent L2R1 record/source/receipt/boundary verifier.
Uses only lane2 files, git objects and process command strings. Does not rebuild,
modify caches, or access the main worktree. Writes its report under /tmp.
"""
import datetime, hashlib, json, pathlib, re, subprocess
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r1')
BASE = '77a9efe144fa706f2b83c6ef4c0096dbfcbf190b'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def declarations(data):
    text = data.decode()
    return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:', text, re.M) +
               re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)', text, re.M))
assert pathlib.Path.cwd() == ROOT
assert git('branch', '--show-current').decode().strip() == 'cp5-thm73-lane-a8a10'
subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, 'HEAD'], cwd=ROOT, check=True)
records = [json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
byunit = {r['unit']: r for r in records}
assert len(byunit) == len(records)
receipts = [json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
bycommit = {r['resultingCommitHash']: r for r in receipts}
assert len(bycommit) == len(receipts)
for r in records:
    assert json.loads((OUT/(r['unit']+'.json')).read_text()) == r
    assert (OUT/(r['unit']+'.log')).read_text() == r['transcript']
    assert sha((OUT/(r['unit']+'.source')).read_bytes()) == r['sourceSHA256']
    assert r['path'] != 'package' and not r['path'].startswith('src/')
    assert r['command'][-2:] == ['--check', str(ROOT/r['path'])]
    assert all('/Work/dgamma/' not in part for part in r['command'])
    if r['passed']:
        assert r['fresh'] and not r['interrupted']
        assert r['exit'] == 0 and not r['expectedDiagnostic'] and 'Error:' not in r['transcript']
        assert re.search(r'^\d+/\d+: Building DGamma\.' + re.escape(pathlib.Path(r['path']).stem) +
                         r' \(' + re.escape(str(ROOT/r['path'])) + r'\)$', r['transcript'], re.M)
    if r['maxSampleRSSKiB'] >= 19*1024*1024:
        assert r.get('heavyLockAcquired'), 'Heavy invocation lacked the shared launch lock'
    if r.get('sourceMutationObserved'):
        assert r['interrupted'] and not r['passed']
for first, second in zip(records, records[1:]):
    assert first['end'] <= second['start'], 'Overlapping compiler invocations'
incidents = json.loads((OUT/'protocol-incidents.json').read_text())
assert byunit['C9-1']['interrupted'] and not byunit['C9-1']['passed']
assert all(not i['preflightCompilerLaunched'] and not i['guardCommitMade'] for i in incidents)
assert 'C10-1' not in byunit, 'This ID is the documented preflight rejection, never a compiler invocation'
sourcecommits = git('log', '--format=%H', BASE+'..HEAD', '--', 'research/', 'research-tests/DGamma/').decode().splitlines()
for commit in sourcecommits:
    receipt = bycommit[commit]
    r = byunit[receipt['invocation']]
    assert receipt['event'] == 'GUARDED COMMIT'
    assert r['passed'] and r['sourceSHA256'] == receipt['sourceHash']
    changed = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).decode().splitlines()
    assert changed == [r['path']]
    new = git('show', commit+':'+r['path'])
    old = subprocess.run(['git', 'show', commit+'^:'+r['path']], cwd=ROOT, capture_output=True).stdout
    assert sha(new) == r['sourceSHA256']
    assert len(declarations(new)-declarations(old)) == 1
    assert r['end'] <= receipt['timestampUTC']
    assert not any(r['end'] < other['start'] < receipt['timestampUTC'] for other in records)
plans = json.loads((OUT/'final-validation-plan.json').read_text())
assert (OUT/'final-validation-plan.json').read_bytes() == (ROOT/'research-tests/O6-L2R1-FINAL-VALIDATION-PLAN.json').read_bytes()
for item in plans:
    r = byunit[item['unit']]
    assert r['passed'] and r['fresh'] and not r['interrupted']
    assert r['path'] == item['path'] and r['sourceSHA256'] == item['sourceHash']
    assert sha((ROOT/r['path']).read_bytes()) == r['sourceSHA256']
paths = git('diff', '--name-only', BASE).decode().splitlines()
allowed = ('research/DGamma/CP5L2R1', 'research-tests/DGamma/L2R1',
           'research-tests/O6-L2R1-', 'research-tests/run-l2r1-')
assert all(p.startswith(allowed) for p in paths)
newdecls = {}
for path in paths:
    if not path.endswith('.idr'):
        continue
    old = subprocess.run(['git', 'show', BASE+':'+path], cwd=ROOT, capture_output=True).stdout
    current = (ROOT/path).read_bytes()
    assert old == b'', 'Only new lane-owned Idris modules permitted'
    assert not re.search(r'\b(believe_me|assert_total|postulate|assert_smaller)\b|\?[A-Za-z_]', current.decode())
    assert '%default total' in current.decode()
    newdecls[path] = sorted(declarations(current)-declarations(old))
    assert any(p['path'] == path for p in plans), 'Missing current-source final fresh check'
assert sum(map(len, newdecls.values())) == len(sourcecommits)
for prefix, cap in [('B', 24), ('C', 20)]:
    attempts = {}
    for r in records:
        match = re.fullmatch(prefix+r'(\d+)-(\d+)', r['unit'])
        if match:
            assert 1 <= int(match[1]) <= cap and 1 <= int(match[2]) <= 3
            attempts.setdefault(match[1], []).append(int(match[2]))
    if prefix == 'C':
        attempts.setdefault('10', []).append(1)  # Rejected preflight conservatively consumes attempt1.
    assert all(len(xs) <= 3 and len(set(xs)) == len(xs) for xs in attempts.values())
assert [r['unit'] for r in records if r['unit'].startswith('B24-')] == ['B24-1', 'B24-2', 'B24-3']
assert all(not byunit['B24-'+str(n)]['passed'] for n in range(1, 4))
assert all('childRemoveAtFound' not in ds for ds in newdecls.values())
assert not git('diff', BASE, '--', 'src/', 'dgamma.ipkg', 'README.md', 'NOTES.md')
assert not git('diff', '--cached', '--name-only')
assert not git('diff', '--name-only'), 'Commit artifacts before independent verification'
processes = subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and
               re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)', row)
               for row in processes.splitlines()), 'Own compiler running'
shift = json.loads((OUT/'shift.json').read_text())
assert all(r['start'] < shift['attemptCutoff'] for r in records if re.fullmatch(r'[BC]\d+-\d+', r['unit']))
assert all(byunit[p['unit']]['end'] < shift['validationCutoff'] for p in plans)
report = dict(status='PASS', head=git('rev-parse', 'HEAD').decode().strip(),
    timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), invocationCount=len(records),
    passedCount=sum(r['passed'] for r in records), failedCount=sum(not r['passed'] for r in records),
    interruptedCount=sum(r['interrupted'] for r in records), finalCheckCount=len(plans),
    newDeclarationCount=sum(map(len, newdecls.values())), newDeclarations=newdecls,
    sourceCommitCount=len(sourcecommits), allSourceCommitsReceiptAuthenticated=True,
    allInvocationsSerialized=True, allRecordedSnapshotsAndLogsAuthenticated=True,
    interruptedC9CompilationSourceIdentityNotAsserted=True,
    protocolIncidents=incidents, preflightRejectedCount=len(incidents),
    allFinalCurrentSourcesAuthenticated=True, productionAndFrozenResearchUntouched=True,
    maxSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records),
    initialRSSQualification='S0-1/S0-2/B1-1 unavailable: pre-fix chez classifier; never a zero-memory claim',
    noUnsafeNewProofs=True, noOwnCompiler=True, noStagedFiles=True, cleanTrackedTree=True,
    manualReviewStillRequired=True)
(OUT/'independent-verification.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({k: v for k, v in report.items() if k != 'newDeclarations'}, indent=2))
