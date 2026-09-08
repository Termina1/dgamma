#!/usr/bin/env python3
"""Commit exactly one source only after an authenticated fresh PASS.
Usage: python3 -I research-tests/run-r186-commit.py UNIT MESSAGE
All checks and git commands share one exception-stopping process.
"""
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
unit, message = sys.argv[1:3]
record = json.loads((pathlib.Path('/tmp/dgamma-r186')/(unit+'.json')).read_text())
assert record['passed'] and record['fresh'] and not record['interrupted']
assert record['exit'] == 0 and not record['expectedDiagnostic']
source = ROOT/record['path']
assert hashlib.sha256(source.read_bytes()).hexdigest() == record['sourceSHA256']
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
processes = subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)',processes)
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
subprocess.run(['git','add','--',record['path']],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m',message],cwd=ROOT,check=True)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
print('GUARDED COMMIT',unit,record['sourceSHA256'])
