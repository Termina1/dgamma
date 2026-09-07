#!/usr/bin/env python3
"""Serialized seeded R178 validation; never deletes TTCs or touches LocalDiamond.
Launch detached with python3 -I. The deadline leaves time for the final audit.
"""
import datetime
import json
import os
import pathlib
import signal
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r178')
DEADLINE = datetime.datetime(2026, 9, 7, 9, 9, tzinfo=datetime.timezone.utc)
PHASES = [
    ('package', ['python3', '-I', 'research-tests/run-r178-check.py', 'F-package', 'package']),
    ('boundaries', ['python3', '-I', 'research-tests/run-r178-boundaries.py']),
    ('legacy-seeded', ['bash', 'research-tests/run-r11-suite.sh']),
]

for name, command in PHASES:
    started = datetime.datetime.now(datetime.timezone.utc)
    if started >= DEADLINE:
        raise SystemExit('Deadline reached before phase ' + name)
    print('PHASE', name, started.isoformat(), flush=True)
    interrupted = False
    with (OUT/('F-'+name+'.log')).open('w') as log:
        process = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        (OUT/'final-active.pid').write_text(str(process.pid))
        while process.poll() is None:
            time.sleep(1)
            if datetime.datetime.now(datetime.timezone.utc) >= DEADLINE and not interrupted:
                interrupted = True
                if name == 'legacy-seeded':
                    os.killpg(process.pid, signal.SIGTERM)
                else:
                    process.send_signal(signal.SIGTERM)
    text = (OUT/('F-'+name+'.log')).read_text()
    passed = process.returncode == 0 and not interrupted
    if name == 'legacy-seeded':
        passed = passed and 'R11_REPRODUCIBLE_SUITE=passed' in text
    record = dict(phase=name, command=command, start=started.isoformat(),
                  end=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  exit=process.returncode, interrupted=interrupted, passed=passed)
    with (OUT/'final-phases.jsonl').open('a') as ledger:
        ledger.write(json.dumps(record)+'\n')
    print('PHASE_RESULT', json.dumps(record), flush=True)
    if not passed:
        print(text[-12000:], flush=True)
        raise SystemExit(1)
print('R178_FINAL_VALIDATION=passed', flush=True)
