#!/usr/bin/env python3
"""Guarded audit/evidence-only commit after an exact-source fresh PASS.
Usage: python3 -I research-tests/run-r195-artifact-commit.py UNIT MESSAGE PATH...
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
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

unit, message, *paths = sys.argv[1:]
recordPath = pathlib.Path('/tmp/dgamma-r195')/(unit+'.json')
record = json.loads(recordPath.read_text())
assert json.loads(pathlib.Path('/tmp/dgamma-r195/ledger.jsonl').read_text().splitlines()[-1])['unit'] == unit, 'No intervening compiler invocation'
assert record['passed'] and record['fresh'] and not record['interrupted']
assert record['exit'] == 0 and not record['expectedDiagnostic']
source = ROOT/('dgamma.ipkg' if record['path'] == 'package' else record['path'])
assert hashlib.sha256(source.read_bytes()).hexdigest() == record['sourceSHA256']
assert paths and all((p.startswith('research-tests/') and not p.endswith('.idr')) or p in ['README.md','NOTES.md','THM73-PLAN.md'] for p in paths)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
assert not subprocess.check_output(['git','diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg'],cwd=ROOT,text=True).strip()
owned_compilers, lane2_compilers, unknown_compilers = compiler_scopes()
assert not owned_compilers and not unknown_compilers, 'Own/unknown compiler active; lane2 is not an orphan'
if lane2_compilers: print('lane-2 compiler (separate worktree)',lane2_compilers,flush=True)
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
subprocess.run(['git','add','--',*paths],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m',message],cwd=ROOT,check=True)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
attemptMatch = re.fullmatch(r'([A-Z]+\d+)-(\d+)', unit)
receipt = dict(event='GUARDED ARTIFACT COMMIT', unit=attemptMatch[1] if attemptMatch else unit, attempt=attemptMatch[2] if attemptMatch else 'not encoded (validation or compiler-free artifact)', invocation=unit, sourceInvocation=record['unit'], sourceHash=record['sourceSHA256'], resultingCommitHash=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), paths=paths, guardChecksPassed=['fresh PASS','exit 0','not interrupted','no expected diagnostic','exact source SHA256','artifact paths only','no source delta','no pre-staged files','no own-worktree compiler (lane2 excluded)','git diff --check','git commit success','no post-staged files'])
with pathlib.Path('/tmp/dgamma-r195/commit-receipts.jsonl').open('a') as ledger:
    ledger.write(json.dumps(receipt)+'\n')
print('GUARDED ARTIFACT COMMIT',json.dumps(receipt),flush=True)
