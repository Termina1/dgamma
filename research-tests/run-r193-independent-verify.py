#!/usr/bin/env python3
"""Read-only R193 receipt/source/validation audit. --interim omits final plan.
No compiler, source/cache mutation, fixed inherited counts, or R192 exceptions.
"""
import datetime, hashlib, json, pathlib, re, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r193')
START = '77a9efe1'
INTERIM = sys.argv[1:] == ['--interim']
assert sys.argv[1:] in [[], ['--interim']]
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def declarations(data):
    text = data.decode()
    return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:', text, re.M) + re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)', text, re.M))
def compiler_scopes():
    owned, lane2, unknown = [], [], []
    for row in subprocess.check_output(['ps','-axo','pid,ppid,command'], text=True).splitlines():
        cells = row.strip().split(None, 2)
        if len(cells) != 3 or not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', cells[2]):
            continue
        probe = subprocess.run(['lsof','-a','-p',cells[0],'-d','cwd','-Fn'],capture_output=True,text=True)
        directories = [line[1:] for line in probe.stdout.splitlines() if line.startswith('n')]
        if str(ROOT)+'/' in cells[2] or str(ROOT) in directories:
            owned.append(row)
        elif '/Users/vyacheslavshebanov/Work/dgamma-lane2/' in cells[2] or '/Users/vyacheslavshebanov/Work/dgamma-lane2' in directories:
            lane2.append(row)
        else:
            unknown.append(row)
    return owned, lane2, unknown
records = [json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
byunit = {r['unit']: r for r in records}
assert len(byunit) == len(records)
receipts = [json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
bycommit = {r['resultingCommitHash']: r for r in receipts}
assert len(bycommit) == len(receipts)
for record in records:
    unit = record['unit']
    assert json.loads((OUT/(unit+'.json')).read_text()) == record, unit
    assert (OUT/(unit+'.log')).read_text() == record['transcript'], unit
    assert sha((OUT/(unit+'.source')).read_bytes()) == record['sourceSHA256'], unit
    if record['passed']:
        assert record['fresh'] and not record['interrupted'], unit
        if record['path'] != 'package':
            relative = re.escape(record['path'])
            absolute = re.escape(str(ROOT/record['path']))
            assert re.search(r'^\d+/\d+: Building [^\n]+ \((?:'+relative+'|'+absolute+r')\)$', record['transcript'], re.M), unit
        if record['expectedDiagnostic']:
            assert record['exit'] != 0 and record['expectedDiagnostic'] in record['transcript'], unit
            assert record.get('symbol') and record['symbol'] in record['transcript'], unit
        else:
            assert record['exit'] == 0 and 'Error:' not in record['transcript'], unit
for first, second in zip(records, records[1:]):
    assert first['end'] <= second['start'], (first['unit'], second['unit'])
sourcecommits = git('log','--format=%H',START+'..HEAD','--','research/','research-tests/DGamma/').decode().splitlines()
for commit in sourcecommits:
    receipt = bycommit[commit]
    record = byunit[receipt['invocation']]
    assert receipt['event'] == 'GUARDED COMMIT', commit
    assert record['passed'] and record['sourceSHA256'] == receipt['sourceHash'], commit
    changed = git('diff-tree','--no-commit-id','--name-only','-r',commit,'--','research/','research-tests/DGamma/').decode().splitlines()
    assert changed == [record['path']], commit
    current = git('show',commit+':'+record['path'])
    prior = subprocess.run(['git','show',commit+'^:'+record['path']],cwd=ROOT,capture_output=True)
    old = prior.stdout if prior.returncode == 0 else b''
    assert len(declarations(current)-declarations(old)) == 1, commit
    assert declarations(old).issubset(declarations(current)), commit
    assert sha(current) == record['sourceSHA256'], commit
    assert record['end'] <= receipt['timestampUTC'], commit
    assert not any(record['end'] < other['start'] < receipt['timestampUTC'] for other in records), commit
attempts = {}
for record in records:
    match = re.fullmatch(r'([A-Z]+\d+)-(\d+)',record['unit'])
    if match:
        attempts.setdefault(match[1], []).append(record)
for unit, runs in attempts.items():
    numbers = [int(r['unit'].rsplit('-',1)[1]) for r in runs]
    assert numbers == list(range(1, len(runs)+1)) and len(runs) <= 3, unit
    assert not any(r['passed'] for r in runs[:-1]), unit
paths = git('diff','--name-only',START,'--','research/','research-tests/DGamma/').decode().splitlines()
newdecls = {}
for path in paths:
    if not path.endswith('.idr'):
        continue
    old = subprocess.run(['git','show',START+':'+path],cwd=ROOT,capture_output=True).stdout
    newdecls[path] = sorted(declarations((ROOT/path).read_bytes())-declarations(old))
assert sum(map(len,newdecls.values())) == len(sourcecommits)
plans = []
substitutions = {}
continuation_hash = None
if not INTERIM:
    plan_bytes = (OUT/'final-validation-plan.json').read_bytes()
    assert plan_bytes == (ROOT/'research-tests/O6-R193-FINAL-VALIDATION-PLAN.json').read_bytes()
    assert sha(plan_bytes) == (OUT/'final-validation-plan.sha256').read_text().strip()
    plans = json.loads(plan_bytes)
    assert len({item['unit'] for item in plans}) == len(plans)
    original_units = [item['unit'] for item in plans]
    if (OUT/'final-validation-continuation.json').exists():
        import runpy
        authenticate = runpy.run_path(str(ROOT/'research-tests/r193_validation_continuation.py'))['authenticate']
        continuation, plans = authenticate(ROOT, OUT)
        substitutions = continuation['substitutions']
        continuation_hash = sha((OUT/'final-validation-continuation.json').read_bytes())
        retry = byunit['V2R1']
        assert retry['rssLimitKiB'] == 52*1024*1024
        assert retry['validationContinuationSHA256'] == continuation_hash
        assert retry['heavyLock'] and retry['heavyLock'][-1]['event'] == 'acquired'
        assert 'HEAVY LOCK RELEASE V2R1' in (OUT/'V2R1.monitor').read_text()
    completion = json.loads((OUT/'final-validation-complete.json').read_text())
    assert completion['invocations'] == [item['unit'] for item in plans]
    assert completion['originalPlanInvocations'] == original_units and completion['substitutions'] == substitutions
    assert completion['serial'] is True
    for item in plans:
        record = byunit[item['unit']]
        assert record['passed'] and record['fresh'] and record['sourceSHA256'] == item['sourceHash'] and record['path'] == item['path']
        assert record.get('rssLimitKiB',48*1024*1024) == (52 if record['unit'] == 'V2R1' else 48)*1024*1024
        assert record['maxSampleRSSKiB'] <= record.get('rssLimitKiB',48*1024*1024)
        assert record['expectedDiagnostic'] == item['expectedDiagnostic'] and record.get('symbol') == item.get('symbol')
        path = 'dgamma.ipkg' if record['path'] == 'package' else record['path']
        assert sha((ROOT/path).read_bytes()) == record['sourceSHA256']
        assert record['start'] < '2026-09-09T00:00:44+00:00'
assert not git('diff','34b21c9','--','src/','dgamma.ipkg')
assert not git('diff','--cached','--name-only')
assert not git('diff','--name-only','--','research/','research-tests/DGamma/','src/','dgamma.ipkg')
if not INTERIM:
    assert not git('diff','--name-only')
assert git('hash-object','src/DGamma/CP3.idr').decode().strip() == '2c697e532e83989de8591fa6a4378747c6a501c0'
owned, lane2, unknown = compiler_scopes()
assert not owned and not unknown, 'Only a separately scoped lane2 compiler may coexist'
report = dict(status='PASS',phase='interim' if INTERIM else 'final',head=git('rev-parse','HEAD').decode().strip(),
    timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),invocationCount=len(records),
    passedCount=sum(r['passed'] for r in records),failedCount=sum(not r['passed'] for r in records),
    expectedNegativeCount=sum(r['passed'] and bool(r['expectedDiagnostic']) for r in records),
    finalCheckCount=len(plans),allFinalCurrentSourcesAuthenticated=not INTERIM,
    finalValidationSubstitutions=substitutions,validationContinuationSHA256=continuation_hash,
    originalResourceStopRetained=('V2' in byunit and byunit['V2']['interrupted']),
    interruptedCount=sum(r['interrupted'] for r in records),
    newDeclarationCount=sum(map(len,newdecls.values())),newDeclarations=newdecls,sourceCommitCount=len(sourcecommits),
    allSourceCommitsReceiptAuthenticated=True,allInvocationsSerializedWithinMainWorktree=True,
    allLogsAndSnapshotsAuthenticated=True,attemptCounts={unit:len(runs) for unit,runs in attempts.items()},
    maxSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records),
    allSourceAttemptsBeforeCutoff=all(r['start']<'2026-09-08T23:45:44+00:00' for runs in attempts.values() for r in runs),
    productionFrozen=True,noUnsafeNewProofs='separate frozen audit enforces prohibition census',
    noCompiler=True,compilerScope='main worktree only',lane2Compilers=lane2,noStagedFiles=True,
    cleanTrackedProofTree=True,cleanTrackedTree=not bool(git('diff','--name-only')))
assert report['allSourceAttemptsBeforeCutoff']
(OUT/('interim-independent-verification.json' if INTERIM else 'independent-verification.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['newDeclarations','attemptCounts']},indent=2))
