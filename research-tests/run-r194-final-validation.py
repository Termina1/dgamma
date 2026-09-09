#!/usr/bin/env python3
"""Detached serial immutable R194 plan. Stop on failure; never retry silently.
Every compiler is launched by python3 -I run-r194-check.py with seeded caches,
its own fresh target observation, mutation/RSS monitor and shared heavy lock.
"""
import datetime, hashlib, json, pathlib, runpy, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r194')
assert not sys.argv[1:]
contract = runpy.run_path(str(ROOT / 'research-tests/r194_evidence_contract.py'))
plan_bytes = (OUT / 'final-validation-plan.json').read_bytes()
assert hashlib.sha256(plan_bytes).hexdigest() == (OUT / 'final-validation-plan.sha256').read_text().strip()
assert plan_bytes == (ROOT / 'research-tests/O6-R194-FINAL-VALIDATION-PLAN.json').read_bytes()
plan = json.loads(plan_bytes)
assert [p['unit'] for p in plan] == ['V' + str(n) for n in range(1, len(plan) + 1)]
assert not (OUT / 'final-validation-complete.json').exists(), 'Append-only completion'
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=ROOT).strip()
assert not subprocess.check_output(['git', 'diff', '--name-only', '--', 'research/', 'src/', 'research-tests/DGamma/'], cwd=ROOT).strip()
for item in plan:
    assert contract['owned_target'](item['path']), 'Only main research roots; inherited baseline variants are allowed'
    source = ROOT / ('dgamma.ipkg' if item['path'] == 'package' else item['path'])
    assert hashlib.sha256(source.read_bytes()).hexdigest() == item['sourceHash']
    assert not (OUT / (item['unit'] + '.json')).exists(), 'No silent overwrite or skip'
    args = ['python3', '-I', str(ROOT / 'research-tests/run-r194-check.py'), item['unit'], item['path']]
    if item['expectedDiagnostic']:
        assert item.get('symbol')
        args += [item['expectedDiagnostic'], item['symbol']]
    print('FINAL START', item['unit'], item['path'], datetime.datetime.now(datetime.timezone.utc).isoformat(), flush=True)
    with (OUT / (item['unit'] + '.monitor')).open('w') as monitor:
        result = subprocess.run(args, cwd=ROOT, stdout=monitor, stderr=subprocess.STDOUT)
    assert (OUT / (item['unit'] + '.json')).exists(), 'No completed record; inspect monitor, no later check started'
    record = json.loads((OUT / (item['unit'] + '.json')).read_text())
    print('FINAL RESULT', item['unit'], json.dumps({k: record[k] for k in ['passed', 'fresh', 'exit', 'seconds', 'maxSampleRSSKiB']}), flush=True)
    if result.returncode or not record['passed'] or not record['fresh']:
        sys.exit('STOP: first final validation failure; no later compiler launched')
(OUT / 'final-validation-complete.json').write_text(json.dumps(dict(completedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    invocations=[p['unit'] for p in plan], serial=True, substitutions={}), indent=2) + '\n')
print('ALL FINAL VALIDATIONS PASSED', len(plan), flush=True)
