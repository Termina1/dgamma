#!/usr/bin/env python3
"""Read-only R194 source/receipt/monitor/validation audit; no compiler or cache writes.
--interim omits final plan completion. A8's two PASSes are accepted ONLY when
exact archived source comparison proves the documented comment-only correction.
"""
import datetime, hashlib, json, pathlib, re, runpy, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r194')
START = 'b81362d8'
INTERIM = sys.argv[1:] == ['--interim']
assert sys.argv[1:] in [[], ['--interim']]
contract = runpy.run_path(str(ROOT / 'research-tests/r194_evidence_contract.py'))
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def declarations(data):
    text = data.decode()
    return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:', text, re.M) + re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)', text, re.M))
def compiler_scopes():
    owned, lane2, unknown = [], [], []
    for row in subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True).splitlines():
        cells = row.strip().split(None, 2)
        if len(cells) != 3 or not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', cells[2]): continue
        probe = subprocess.run(['lsof', '-a', '-p', cells[0], '-d', 'cwd', '-Fn'], capture_output=True, text=True)
        directories = [line[1:] for line in probe.stdout.splitlines() if line.startswith('n')]
        if str(ROOT) + '/' in cells[2] or str(ROOT) in directories: owned.append(row)
        elif '/Users/vyacheslavshebanov/Work/dgamma-lane2/' in cells[2] or '/Users/vyacheslavshebanov/Work/dgamma-lane2' in directories: lane2.append(row)
        else: unknown.append(row)
    return owned, lane2, unknown
records = [json.loads(s) for s in (OUT / 'ledger.jsonl').read_text().splitlines()]
byunit = {r['unit']: r for r in records}
assert len(byunit) == len(records)
receipts = [json.loads(s) for s in (OUT / 'commit-receipts.jsonl').read_text().splitlines()]
bycommit = {r['resultingCommitHash']: r for r in receipts}
assert len(bycommit) == len(receipts)
snapshots = {}
for record in records:
    unit = record['unit']
    assert json.loads((OUT / (unit + '.json')).read_text()) == record
    snapshots[unit] = (OUT / (unit + '.source')).read_bytes()
    contract['validate_record'](record, snapshots[unit], (OUT / (unit + '.log')).read_text(), ROOT)
for first, second in zip(records, records[1:]):
    assert first['end'] <= second['start'], (first['unit'], second['unit'])
sourcecommits = git('log', '--format=%H', START + '..HEAD', '--', 'research/', 'research-tests/DGamma/').decode().splitlines()
for commit in sourcecommits:
    receipt = bycommit[commit]
    record = byunit[receipt['invocation']]
    assert receipt['event'] == 'GUARDED COMMIT' and record['passed'] and record['sourceSHA256'] == receipt['sourceHash']
    changed = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit, '--', 'research/', 'research-tests/DGamma/').decode().splitlines()
    assert changed == [record['path']], commit
    current = git('show', commit + ':' + record['path'])
    prior = subprocess.run(['git', 'show', commit + '^:' + record['path']], cwd=ROOT, capture_output=True)
    old = prior.stdout if prior.returncode == 0 else b''
    assert len(declarations(current) - declarations(old)) == 1 and declarations(old).issubset(declarations(current)), commit
    assert sha(current) == record['sourceSHA256'] and record['end'] <= receipt['timestampUTC']
    assert not any(record['end'] < other['start'] < receipt['timestampUTC'] for other in records), commit
attempts = contract['validate_attempts'](records, snapshots)
paths = git('diff', '--name-only', START, '--', 'research/', 'research-tests/DGamma/').decode().splitlines()
newdecls = {}
for path in paths:
    if path.endswith('.idr'):
        old = subprocess.run(['git', 'show', START + ':' + path], cwd=ROOT, capture_output=True).stdout
        newdecls[path] = sorted(declarations((ROOT / path).read_bytes()) - declarations(old))
assert sum(map(len, newdecls.values())) == len(sourcecommits) == 46
assert sum(unit.startswith('A') for unit in attempts) == 30 and sum(unit.startswith('B') for unit in attempts) == 16
plans = []
if not INTERIM:
    plan_bytes = (OUT / 'final-validation-plan.json').read_bytes()
    assert plan_bytes == (ROOT / 'research-tests/O6-R194-FINAL-VALIDATION-PLAN.json').read_bytes()
    assert sha(plan_bytes) == (OUT / 'final-validation-plan.sha256').read_text().strip()
    plans = json.loads(plan_bytes)
    assert [p['unit'] for p in plans] == ['V' + str(n) for n in range(1, len(plans) + 1)]
    assert len(plans) == 59
    prior = (ROOT / 'research-tests/O6-R194-PREFLIGHT-PLAN.json').read_bytes()
    assert sha(prior) == '73ddfc58ea6e13473f31a61366fcbad931a18cc69b62b1de6ceb58985fa31bfe'
    assert prior == (OUT / 'preflight-plan.json').read_bytes()
    scope = json.loads((ROOT / 'research-tests/O6-R194-FINAL-VALIDATION-SCOPE.json').read_text())
    assert scope == json.loads((OUT / 'final-validation-scope.json').read_text()) and scope['exclusions'] == []
    inherited = json.loads((ROOT / 'research-tests/O6-R193-FINAL-VALIDATION-PLAN.json').read_text())
    assert {p['path'] for p in inherited}.issubset({p['path'] for p in plans})
    for item in inherited:
        target = 'dgamma.ipkg' if item['path'] == 'package' else item['path']
        assert (ROOT / target).read_bytes() == git('show', START + ':' + target)
    completion = json.loads((OUT / 'final-validation-complete.json').read_text())
    assert completion['invocations'] == [p['unit'] for p in plans] and completion['serial'] and completion['substitutions'] == {}
    assert {r['unit'] for r in records if r['unit'].startswith('V')} == {p['unit'] for p in plans}
    covered = {p['path'] for p in plans}
    assert set(newdecls).issubset(covered) and 'package' in covered
    assert all('research/DGamma/CP5Confluence' + p + 'Spike.idr' in covered for p in ['LocalDiamond', 'DeletionChain', 'CanonicalSort', 'RenamingComposition', 'CrossTrace'])
    for item in plans:
        r = byunit[item['unit']]
        assert r['passed'] and r['fresh'] and r['sourceSHA256'] == item['sourceHash'] and r['path'] == item['path']
        assert r['expectedDiagnostic'] == item['expectedDiagnostic'] and r.get('symbol') == item.get('symbol')
        target = 'dgamma.ipkg' if r['path'] == 'package' else r['path']
        assert sha((ROOT / target).read_bytes()) == r['sourceSHA256']
        limit = (52 if 'CP5ConfluenceLocalDiamondSpike.idr' in target else 48) * 1024 * 1024
        assert r['rssLimitKiB'] == limit and r['maxSampleRSSKiB'] <= limit
        if 'CP5ConfluenceLocalDiamondSpike.idr' in target:
            assert snapshots[r['unit']] == git('show', START + ':' + target)
            assert r['heavyLock'] and r['heavyLock'][-1]['event'] == 'acquired'
            assert 'HEAVY LOCK RELEASE ' + r['unit'] in (OUT / (r['unit'] + '.monitor')).read_text()
        assert scope['timestampUTC'] <= r['start'] < '2026-09-09T03:28:53+00:00'
assert not git('diff', '34b21c9', '--', 'src/', 'dgamma.ipkg')
assert not git('diff', '--cached', '--name-only')
assert not git('diff', '--name-only', '--', 'research/', 'research-tests/DGamma/', 'src/', 'dgamma.ipkg')
if not INTERIM: assert not git('diff', '--name-only')
assert git('hash-object', 'src/DGamma/CP3.idr').decode().strip() == '2c697e532e83989de8591fa6a4378747c6a501c0'
owned, lane2, unknown = compiler_scopes()
assert not owned and not unknown
report = dict(status='PASS', phase='interim' if INTERIM else 'final', head=git('rev-parse', 'HEAD').decode().strip(),
    timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), invocationCount=len(records),
    passedCount=sum(r['passed'] for r in records), failedCount=sum(not r['passed'] for r in records),
    expectedNegativeCount=sum(r['passed'] and bool(r['expectedDiagnostic']) for r in records),
    finalCheckCount=len(plans), allFinalCurrentSourcesAuthenticated=not INTERIM,
    interruptedCount=sum(r['interrupted'] for r in records), targetMutationCount=sum(r['targetMutationDetected'] for r in records),
    allRSSSamplesAuthenticated=True, maxSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records),
    successfulRecheckQualification='A8-1/A8-2: both PASS, exact code unchanged, documented docstring correction only',
    newDeclarationCount=sum(map(len, newdecls.values())), newDeclarations=newdecls, sourceCommitCount=len(sourcecommits),
    changedIdrisTargetCount=len(newdecls), allChangedIdrisTargetsHaveOwnFinalCheck=not INTERIM,
    allSourceCommitsReceiptAuthenticated=True, allInvocationsSerializedWithinMainWorktree=True,
    allLogsAndSnapshotsAuthenticated=True, attemptCounts={unit: len(runs) for unit, runs in attempts.items()},
    allSourceAttemptsBeforeCutoff=all(r['start'] < '2026-09-09T03:13:53+00:00' for runs in attempts.values() for r in runs),
    productionFrozen=True, noCompiler=True, compilerScope='main worktree only', lane2Compilers=lane2,
    noLane2CreatedResultsChecked=True, inheritedMainBaselineTargetsIncluded=not INTERIM,
    noStagedFiles=True, cleanTrackedProofTree=True, cleanTrackedTree=not bool(git('diff', '--name-only')))
assert report['allSourceAttemptsBeforeCutoff']
(OUT / ('interim-independent-verification.json' if INTERIM else 'independent-verification.json')).write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k not in ['newDeclarations', 'attemptCounts']}, indent=2))
