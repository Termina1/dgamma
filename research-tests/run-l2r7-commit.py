#!/usr/bin/env python3
"""Commit one declaration after fresh PASS; no companion bundle is currently authorized.
Usage: python3 -I research-tests/run-l2r7-commit.py UNIT MESSAGE
All checks and git commands share one exception-stopping process.
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
unit, message = sys.argv[1:3]
record = json.loads((pathlib.Path('/tmp/dgamma-l2r7')/(unit+'.json')).read_text())
assert record['passed'] and record['fresh'] and not record['interrupted'] and not record['sourceMutationObserved']
assert record['exit'] == 0 and not record['expectedDiagnostic']
assert json.loads(pathlib.Path('/tmp/dgamma-l2r7/ledger.jsonl').read_text().splitlines()[-1])['unit'] == unit, 'No intervening compiler invocation'
# The ONLY declaration-publication validation exception is B2's exact EOF trim.
# Final V10+ checks cannot bypass proof-unit attempt/cap accounting.
if unit.startswith('V'):
 assert unit == 'V1', 'Only the archived B2 whitespace validation may publish a declaration'
 prior = json.loads(pathlib.Path('/tmp/dgamma-l2r7/B2-1.json').read_text())
 assert prior['passed'] and prior['fresh'] and record['path'] == prior['path']
 assert (ROOT/record['path']).read_bytes() == pathlib.Path('/tmp/dgamma-l2r7/B2-1.source').read_bytes().rstrip()+b'\n'
old = subprocess.run(['git','show','HEAD:'+record['path']],cwd=ROOT,capture_output=True)
def declarations(data):
    text = data.decode()
    return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M) + re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
assert len(declarations((ROOT/record['path']).read_bytes())-declarations(old.stdout if old.returncode == 0 else b'')) == 1, 'Exactly one new declaration in source commit'
assert record['path'].startswith(('research-tests/O6-L2R7-Sources/',)), 'Lane-owned source only'
source = ROOT/record['path']
commitPaths=[record['path']]
assert not record.get('bundleSources'), 'No companion bundle authorized'
if record.get('bundleSources'):
 assert record['bundleFresh']
 for extra in record['bundleSources']:
  assert hashlib.sha256((ROOT/extra['path']).read_bytes()).hexdigest()==extra['sourceSHA256']
  commitPaths.append(extra['path'])
assert hashlib.sha256(source.read_bytes()).hexdigest() == record['sourceSHA256']
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
processes = subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines()), 'Own compiler running; main-lane compilers are separate'
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip() == 'cp5-thm73-lane-a8a10'
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
subprocess.run(['git','add','--',*commitPaths],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m',message],cwd=ROOT,check=True)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
receipt = dict(paths=commitPaths,sourceHashes={record['path']:record['sourceSHA256'],**{x['path']:x['sourceSHA256'] for x in record.get('bundleSources',[])}},event='GUARDED COMMIT', unit=unit.rsplit('-',1)[0], attempt=unit.rsplit('-',1)[1] if '-' in unit else 'validation', invocation=unit, sourceHash=record['sourceSHA256'], resultingCommitHash=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), guardChecksPassed=['fresh PASS','exit 0','not interrupted','no expected diagnostic','exact source SHA256','one new declaration','no intervening compiler invocation','no pre-staged files','no compiler','git diff --check','git commit success','no post-staged files'])
with pathlib.Path('/tmp/dgamma-l2r7/commit-receipts.jsonl').open('a') as ledger:
    ledger.write(json.dumps(receipt)+'\n')
print('GUARDED COMMIT',json.dumps(receipt),flush=True)
