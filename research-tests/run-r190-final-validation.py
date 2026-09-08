#!/usr/bin/env python3
"""Detached serial final validations from the immutable R190 plan.
Each source/package check uses the guarded seeded runner and its own monitor.
Stops on the first failure; never edits Idris source, deletes TTC, or overlaps
compilers. R190 proof stop and all-start cutoff are enforced by the check runner.
"""
import datetime
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r190')
phase=sys.argv[1]
assert phase in ['prebody','postbody']
plan = json.loads((OUT/(phase+'-validation-plan.json')).read_text())
assert len({p['unit'] for p in plan}) == len(plan)
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=ROOT).strip()
assert not subprocess.check_output(['git', 'diff', '--name-only', '--', 'research/', 'src/', 'research-tests/DGamma/'], cwd=ROOT).strip()
processes = subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True)
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', processes)
for item in plan:
    assert re.fullmatch(r'V\d+', item['unit'])
    assert not (OUT/(item['unit']+'.json')).exists(), 'Final plan never silently overwrites or skips an invocation'
    args = ['python3', '-I', str(ROOT/'research-tests/run-r190-check.py'), item['unit'], item['path']]
    if item['expectedDiagnostic']:
        args.append(item['expectedDiagnostic'])
    print('FINAL START', item['unit'], item['path'], datetime.datetime.now(datetime.timezone.utc).isoformat(), flush=True)
    with (OUT/(item['unit']+'.monitor')).open('w') as monitor:
        result = subprocess.run(args, cwd=ROOT, stdout=monitor, stderr=subprocess.STDOUT)
    assert (OUT/(item['unit']+'.json')).exists(), 'Runner refused or did not finish; inspect its monitor'
    record = json.loads((OUT/(item['unit']+'.json')).read_text())
    print('FINAL RESULT', item['unit'], json.dumps({k:record[k] for k in ['passed', 'fresh', 'exit', 'seconds', 'maxSampleRSSKiB']}), flush=True)
    if result.returncode or not record['passed'] or not record['fresh']:
        print('STOP: first final validation failure, no later compiler launched', flush=True)
        sys.exit(1)
(OUT/(phase+'-validation-complete.json')).write_text(json.dumps(dict(completedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), invocations=[p['unit'] for p in plan], serial=True), indent=2)+'\n')
print('ALL FINAL VALIDATIONS PASSED', len(plan), flush=True)
