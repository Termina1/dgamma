#!/usr/bin/env python3
"""Run an immutable leaf-before-dependent plan serially, detached, Python -I.
Only the final L2R6 plan is authorized; no addendum/source cap extension.
No source contents are changed; each checker performs the approved target-only
mtime touch. Stop on the first non-PASS, never silently rerun an invocation ID.
"""
import hashlib, json, pathlib, subprocess, sys
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r6')
assert pathlib.Path.cwd() == ROOT
assert sys.argv[1:] == []
localPlan, committedPlan = 'final-validation-plan.json','research-tests/O6-L2R6-FINAL-VALIDATION-PLAN.json'
plan = json.loads((OUT/localPlan).read_text())
assert (OUT/localPlan).read_bytes() == (ROOT/committedPlan).read_bytes()
for item in plan:
    assert hashlib.sha256((ROOT/item['path']).read_bytes()).hexdigest() == item['sourceHash']
    assert not (OUT/(item['unit']+'.json')).exists()
for item in plan:
    with (OUT/(item['unit']+'.wrapper.log')).open('w') as log:
        outcome = subprocess.run([sys.executable, '-I', str(ROOT/'research-tests/run-l2r6-check.py'),
                                  item['unit'], item['path']], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    print(item['unit'], item['path'], 'wrapper-exit', outcome.returncode, flush=True)
    assert outcome.returncode == 0, 'Stopped at non-PASS; do not continue or mutate the immutable plan'
    record = json.loads((OUT/(item['unit']+'.json')).read_text())
    assert record['passed'] and record['fresh'] and not record['sourceMutationObserved'] and record['sourceSHA256'] == item['sourceHash']
print('ALL', len(plan), 'IMMUTABLE FINAL CHECKS FRESH-PASS', flush=True)
