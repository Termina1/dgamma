#!/usr/bin/env python3
"""Detached serial final validations from the immutable R193 plan.
Each source/package check uses the guarded seeded runner and its own monitor.
Stops on the first failure; never edits Idris source, deletes TTC, or overlaps
compilers. R193 proof stop and all-start cutoff are enforced by the check runner.
"""
import datetime
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r193')

def compiler_scopes():
    owned, lane2, unknown = [], [], []
    for row in subprocess.check_output(['ps','-axo','pid,ppid,command'], text=True).splitlines():
        cells = row.strip().split(None, 2)
        if len(cells) != 3 or not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', cells[2]):
            continue
        cwd_probe = subprocess.run(['lsof','-a','-p',cells[0],'-d','cwd','-Fn'],capture_output=True,text=True)
        directories = [line[1:] for line in cwd_probe.stdout.splitlines() if line.startswith('n')]
        if str(ROOT)+'/' in cells[2] or str(ROOT) in directories:
            owned.append(row)
        elif '/Users/vyacheslavshebanov/Work/dgamma-lane2/' in cells[2] or '/Users/vyacheslavshebanov/Work/dgamma-lane2' in directories:
            lane2.append(row)
        else:
            unknown.append(row)
    return owned, lane2, unknown

phase=sys.argv[1]
assert phase in ['final', 'continue']
plan_stem = 'final-validation'
plan = json.loads((OUT/(plan_stem+'-plan.json')).read_text())
original_units = [p['unit'] for p in plan]
substitutions = {}
effective_plan = plan
if phase == 'continue':
    import runpy
    authenticate = runpy.run_path(str(ROOT/'research-tests/r193_validation_continuation.py'))['authenticate']
    continuation, effective_plan = authenticate(ROOT, OUT)
    substitutions = continuation['substitutions']
    plan = effective_plan[1:]
assert len({p['unit'] for p in plan}) == len(plan)
assert not (OUT/(plan_stem+'-complete.json')).exists(), 'Completion records are append-only'
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=ROOT).strip()
assert not subprocess.check_output(['git', 'diff', '--name-only', '--', 'research/', 'src/', 'research-tests/DGamma/'], cwd=ROOT).strip()
owned_compilers,lane2_compilers,unknown_compilers=compiler_scopes()
assert not owned_compilers and not unknown_compilers
if lane2_compilers:print('lane-2 compiler (separate worktree)',lane2_compilers,flush=True)
for item in plan:
    assert re.fullmatch(r'V\d+', item['unit']) or (phase == 'continue' and item['unit'] == 'V2R1')
    import hashlib
    source = ROOT/('dgamma.ipkg' if item['path']=='package' else item['path'])
    assert hashlib.sha256(source.read_bytes()).hexdigest() == item['sourceHash'], 'Immutable final source changed'
    assert not (OUT/(item['unit']+'.json')).exists(), 'Final plan never silently overwrites or skips an invocation'
    args = ['python3', '-I', str(ROOT/'research-tests/run-r193-check.py'), item['unit'], item['path']]
    if item['expectedDiagnostic']:
        args.append(item['expectedDiagnostic'])
        assert item.get('symbol'), 'Expected negative requires its authenticated declaration symbol'
        args.append(item['symbol'])
    print('FINAL START', item['unit'], item['path'], datetime.datetime.now(datetime.timezone.utc).isoformat(), flush=True)
    with (OUT/(item['unit']+'.monitor')).open('w') as monitor:
        result = subprocess.run(args, cwd=ROOT, stdout=monitor, stderr=subprocess.STDOUT)
    assert (OUT/(item['unit']+'.json')).exists(), 'Runner refused or did not finish; inspect its monitor'
    record = json.loads((OUT/(item['unit']+'.json')).read_text())
    print('FINAL RESULT', item['unit'], json.dumps({k:record[k] for k in ['passed', 'fresh', 'exit', 'seconds', 'maxSampleRSSKiB']}), flush=True)
    if result.returncode or not record['passed'] or not record['fresh']:
        print('STOP: first final validation failure, no later compiler launched', flush=True)
        sys.exit(1)
(OUT/(plan_stem+'-complete.json')).write_text(json.dumps(dict(completedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), invocations=[p['unit'] for p in effective_plan], originalPlanInvocations=original_units, substitutions=substitutions, serial=True), indent=2)+'\n')
print('ALL EFFECTIVE FINAL VALIDATIONS PASSED', len(effective_plan), 'substitutions', substitutions, flush=True)
