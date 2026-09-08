#!/usr/bin/env python3
"""Guarded audit/evidence-only commit after an exact-source fresh PASS.
Usage: python3 -I research-tests/run-r186-artifact-commit.py UNIT MESSAGE PATH...
"""
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
unit, message, *paths = sys.argv[1:]
record = json.loads((pathlib.Path('/tmp/dgamma-r186')/(unit+'.json')).read_text())
assert record['passed'] and record['fresh'] and not record['interrupted']
assert record['exit'] == 0 and not record['expectedDiagnostic']
source = ROOT/('dgamma.ipkg' if record['path'] == 'package' else record['path'])
assert hashlib.sha256(source.read_bytes()).hexdigest() == record['sourceSHA256']
assert paths and all(p.startswith('research-tests/') and not p.endswith('.idr') for p in paths)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
assert not subprocess.check_output(['git','diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg'],cwd=ROOT,text=True).strip()
processes = subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)',processes)
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
subprocess.run(['git','add','--',*paths],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m',message],cwd=ROOT,check=True)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
print('GUARDED ARTIFACT COMMIT',unit,record['sourceSHA256'])
