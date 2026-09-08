#!/usr/bin/env python3
"""Guarded audit/evidence-only commit after an exact-source fresh PASS.
Usage: python3 -I research-tests/run-l2r1-artifact-commit.py UNIT MESSAGE PATH...
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
unit, message, *paths = sys.argv[1:]
recordPath = pathlib.Path('/tmp/dgamma-l2r1')/(unit+'.json')
record = json.loads(recordPath.read_text())
assert record['passed'] and record['fresh'] and not record['interrupted']
assert record['exit'] == 0 and not record['expectedDiagnostic']
source = ROOT/('dgamma.ipkg' if record['path'] == 'package' else record['path'])
assert hashlib.sha256(source.read_bytes()).hexdigest() == record['sourceSHA256']
assert paths and all(p.startswith(('research-tests/O6-L2R1-', 'research-tests/run-l2r1-')) and not p.endswith('.idr') for p in paths)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
assert not subprocess.check_output(['git','diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg'],cwd=ROOT,text=True).strip()
processes = subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines()), 'Own compiler running; main-lane compilers are separate'
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip() == 'cp5-thm73-lane-a8a10'
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
subprocess.run(['git','add','--',*paths],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m',message],cwd=ROOT,check=True)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
attemptMatch = re.fullmatch(r'([A-Z]+\d+)-(\d+)', unit)
receipt = dict(event='GUARDED ARTIFACT COMMIT', unit=attemptMatch[1] if attemptMatch else unit, attempt=attemptMatch[2] if attemptMatch else 'not encoded (validation or compiler-free artifact)', invocation=unit, sourceInvocation=record['unit'], sourceHash=record['sourceSHA256'], resultingCommitHash=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), paths=paths, guardChecksPassed=['fresh PASS','exit 0','not interrupted','no expected diagnostic','exact source SHA256','artifact paths only','no source delta','no pre-staged files','no compiler','git diff --check','git commit success','no post-staged files'])
with pathlib.Path('/tmp/dgamma-l2r1/commit-receipts.jsonl').open('a') as ledger:
    ledger.write(json.dumps(receipt)+'\n')
print('GUARDED ARTIFACT COMMIT',json.dumps(receipt),flush=True)
